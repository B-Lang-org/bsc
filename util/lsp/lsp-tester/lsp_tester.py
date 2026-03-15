#!/usr/bin/env python3
"""
lsp-tester — integration test harness for bs-lsp.

Single-file mode:
  python3 lsp_tester.py [OPTIONS] FILE.bsv

Batch mode (one LSP session for all files — efficient for hundreds of files):
  python3 lsp_tester.py [OPTIONS] --dirs DIR [DIR ...] [FILE ...]
  python3 lsp_tester.py [OPTIONS] --dirs /work/Flute /work/Toooba --log results.jsonl

Starts bs-lsp, opens BSV/BS source files, and systematically tests
textDocument/hover (type inference) and textDocument/definition (go-to-def)
for sampled identifier positions.  Follows definitions across file boundaries
up to a configurable depth, watching for server crashes.

In batch mode the LSP is started once and a global visited-position set
prevents retesting the same (file, line, col) twice — so stdlib files that
are reached from many different seed files are only tested once.

Exit codes:
  0  No crashes detected
  1  One or more crashes detected
  2  Tool error (binary not found, file unreadable, LSP won't start, etc.)
"""

import argparse
import datetime
import json
import logging
import os
import re
import subprocess
import sys
import threading
import time
from collections import deque
from dataclasses import dataclass, field
from pathlib import Path
from queue import Empty, Queue
from typing import Optional
from urllib.parse import unquote, urlparse

# ── Exit codes ────────────────────────────────────────────────────────────────
EXIT_OK = 0
EXIT_CRASHES = 1
EXIT_TOOL_ERROR = 2

# ── Progress symbols ──────────────────────────────────────────────────────────
SYM = {"ok": "✓", "null": "·", "crash": "💥", "timeout": "⏱", "error": "!"}

log = logging.getLogger("lsp-tester")


# ── URI helpers ───────────────────────────────────────────────────────────────

def uri_to_path(uri: str) -> str:
    return unquote(urlparse(uri).path)

def path_to_uri(path: str) -> str:
    return Path(path).resolve().as_uri()

def relpath(path: str) -> str:
    try:
        return str(Path(path).relative_to(Path.cwd()))
    except ValueError:
        return path

def now_iso() -> str:
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


# ── JSON-RPC framing ──────────────────────────────────────────────────────────

def _encode(obj: dict) -> bytes:
    body = json.dumps(obj, separators=(",", ":")).encode("utf-8")
    return f"Content-Length: {len(body)}\r\n\r\n".encode() + body

class _MessageBuffer:
    def __init__(self):
        self._buf = b""

    def feed(self, data: bytes) -> list[dict]:
        self._buf += data
        msgs = []
        while True:
            idx = self._buf.find(b"\r\n\r\n")
            if idx == -1:
                break
            header_block = self._buf[:idx]
            m = re.search(rb"Content-Length:\s*(\d+)", header_block, re.IGNORECASE)
            if not m:
                self._buf = self._buf[idx + 4:]
                continue
            length = int(m.group(1))
            body_end = idx + 4 + length
            if len(self._buf) < body_end:
                break
            body = self._buf[idx + 4:body_end]
            self._buf = self._buf[body_end:]
            try:
                msgs.append(json.loads(body))
            except json.JSONDecodeError as e:
                log.debug("JSON decode error: %s", e)
        return msgs


# ── LSP process wrapper ───────────────────────────────────────────────────────

class LspProcess:
    def __init__(self, binary: str, env: dict, request_timeout: float = 12.0):
        self.binary = binary
        self.env = env
        self.request_timeout = request_timeout
        self._proc: Optional[subprocess.Popen] = None
        self._msg_q: Queue = Queue()
        self._req_id = 0
        self._id_lock = threading.Lock()
        self._stderr_buf: deque = deque(maxlen=400)

    def start(self) -> bool:
        try:
            self._proc = subprocess.Popen(
                [self.binary], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                stderr=subprocess.PIPE, env=self.env, bufsize=0,
            )
        except (FileNotFoundError, PermissionError, OSError) as e:
            log.error("Cannot start %s: %s", self.binary, e)
            return False
        threading.Thread(target=self._read_stdout, daemon=True).start()
        threading.Thread(target=self._read_stderr, daemon=True).start()
        return True

    def _read_stdout(self):
        buf = _MessageBuffer()
        while True:
            try:
                chunk = self._proc.stdout.read(4096)
            except Exception:
                break
            if not chunk:
                break
            for msg in buf.feed(chunk):
                self._msg_q.put(msg)

    def _read_stderr(self):
        try:
            for raw in self._proc.stderr:
                line = raw.decode("utf-8", errors="replace").rstrip()
                self._stderr_buf.append(line)
                log.debug("stderr: %s", line)
        except Exception:
            pass

    def is_alive(self) -> bool:
        return self._proc is not None and self._proc.poll() is None

    def recent_stderr(self, n: int = 30) -> list[str]:
        return list(self._stderr_buf)[-n:]

    def _next_id(self) -> int:
        with self._id_lock:
            self._req_id += 1
            return self._req_id

    def notify(self, method: str, params) -> bool:
        if not self.is_alive():
            return False
        try:
            self._proc.stdin.write(_encode({"jsonrpc": "2.0", "method": method, "params": params}))
            self._proc.stdin.flush()
            return True
        except (BrokenPipeError, OSError):
            return False

    def request(self, method: str, params) -> Optional[dict]:
        req_id = self._next_id()
        if not self.is_alive():
            return None
        try:
            self._proc.stdin.write(_encode({"jsonrpc": "2.0", "id": req_id, "method": method, "params": params}))
            self._proc.stdin.flush()
        except (BrokenPipeError, OSError):
            return None
        deadline = time.monotonic() + self.request_timeout
        while time.monotonic() < deadline:
            if not self.is_alive():
                return None
            try:
                resp = self._msg_q.get(timeout=0.15)
            except Empty:
                continue
            if "method" in resp and "id" not in resp:
                continue  # skip notifications
            if resp.get("id") == req_id:
                return resp
        return None  # timeout

    def stop(self):
        if not self.is_alive():
            return
        try:
            self.request("shutdown", None)
            self.notify("exit", None)
            self._proc.wait(timeout=4)
        except Exception:
            pass
        if self.is_alive():
            try:
                self._proc.kill()
            except Exception:
                pass


# ── LSP session ───────────────────────────────────────────────────────────────

class LspSession:
    def __init__(self, proc: LspProcess, workspace: str):
        self.proc = proc
        self.workspace = workspace
        self._open_docs: set[str] = set()

    def initialize(self) -> bool:
        resp = self.proc.request("initialize", {
            "processId": os.getpid(),
            "rootUri": path_to_uri(self.workspace),
            "rootPath": self.workspace,
            "capabilities": {
                "textDocument": {
                    "hover": {"contentFormat": ["markdown", "plaintext"]},
                    "definition": {},
                    "documentSymbol": {},
                },
                "workspace": {"workspaceFolders": True},
            },
            "workspaceFolders": [{"uri": path_to_uri(self.workspace), "name": Path(self.workspace).name}],
        })
        if resp is None or "error" in resp:
            log.error("initialize failed: %s", resp)
            return False
        self.proc.notify("initialized", {})
        time.sleep(0.4)
        return True

    def open_document(self, file_path: str) -> bool:
        abs_path = str(Path(file_path).resolve())
        if abs_path in self._open_docs:
            return True
        try:
            text = Path(abs_path).read_text(errors="replace")
        except OSError as e:
            log.warning("Cannot read %s: %s", abs_path, e)
            return False
        ext = Path(abs_path).suffix.lower()
        ok = self.proc.notify("textDocument/didOpen", {
            "textDocument": {
                "uri": path_to_uri(abs_path),
                "languageId": "bluespec" if ext == ".bs" else "bluespec-sv",
                "version": 1,
                "text": text,
            }
        })
        if ok:
            self._open_docs.add(abs_path)
            time.sleep(0.1)
        return ok

    def hover(self, file_path: str, line: int, char: int) -> tuple[str, Optional[str]]:
        abs_path = str(Path(file_path).resolve())
        resp = self.proc.request("textDocument/hover", {
            "textDocument": {"uri": path_to_uri(abs_path)},
            "position": {"line": line, "character": char},
        })
        return self._decode_hover(resp)

    def definition(self, file_path: str, line: int, char: int) -> tuple[str, Optional[dict]]:
        abs_path = str(Path(file_path).resolve())
        resp = self.proc.request("textDocument/definition", {
            "textDocument": {"uri": path_to_uri(abs_path)},
            "position": {"line": line, "character": char},
        })
        return self._decode_definition(resp)

    def _decode_hover(self, resp):
        if resp is None:
            return ("crash" if not self.proc.is_alive() else "timeout"), None
        if "error" in resp:
            return "error", str(resp["error"])
        result = resp.get("result")
        if result is None:
            return "null", None
        contents = result.get("contents", "")
        if isinstance(contents, dict):
            text = contents.get("value", "")
        elif isinstance(contents, list):
            text = " | ".join(c.get("value", "") if isinstance(c, dict) else str(c) for c in contents)
        else:
            text = str(contents)
        return ("ok", text.strip()) if text.strip() else ("null", None)

    def _decode_definition(self, resp):
        if resp is None:
            return ("crash" if not self.proc.is_alive() else "timeout"), None
        if "error" in resp:
            return "error", None
        result = resp.get("result")
        if result is None:
            return "null", None
        if isinstance(result, list):
            result = result[0] if result else None
        if not result or not isinstance(result, dict):
            return "null", None
        uri = result.get("uri", "")
        start = result.get("range", {}).get("start", {})
        return "ok", {
            "uri": uri, "path": uri_to_path(uri),
            "line": start.get("line", 0), "character": start.get("character", 0),
        }


# ── Identifier scanning ───────────────────────────────────────────────────────

_SKIP_WORDS = frozenset({
    "module", "endmodule", "interface", "endinterface", "method", "endmethod",
    "rule", "endrule", "action", "endaction", "actionvalue", "endactionvalue",
    "function", "endfunction", "package", "endpackage", "instance", "endinstance",
    "typeclass", "endtypeclass", "if", "else", "begin", "end", "case", "endcase",
    "of", "let", "in", "where", "do", "return", "import", "export", "type",
    "typedef", "struct", "enum", "union", "tagged", "deriving", "provisos",
    "for", "while", "seq", "endseq", "par", "endpar", "match", "matches",
    "numeric", "void", "Bool", "True", "False", "Integer", "String",
})
_IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
_LINE_COMMENT_RE = re.compile(r"//.*$")
_BLOCK_COMMENT_RE = re.compile(r"/\*.*?\*/", re.DOTALL)
_STRING_LIT_RE = re.compile(r'"[^"\\]*(?:\\.[^"\\]*)*"')

def scan_identifiers(text: str, max_count: int = 40) -> list[tuple[int, int, str]]:
    clean = _BLOCK_COMMENT_RE.sub(lambda m: "\n" * m.group().count("\n"), text)
    lines = clean.splitlines()
    candidates: list[tuple[int, int, str]] = []
    seen: set[str] = set()
    for lineno, line in enumerate(lines):
        lc = _LINE_COMMENT_RE.sub("", line)
        lc = _STRING_LIT_RE.sub("", lc)
        for m in _IDENT_RE.finditer(lc):
            name = m.group()
            if name in _SKIP_WORDS or name in seen:
                continue
            seen.add(name)
            candidates.append((lineno, m.start(), name))
    if len(candidates) <= max_count:
        return candidates
    step = len(candidates) / max_count
    return [candidates[int(i * step)] for i in range(max_count)]


# ── Result types ──────────────────────────────────────────────────────────────

@dataclass
class TestResult:
    file_path: str
    line: int
    char: int
    name: str
    hover_status: str = "untested"
    hover_text: str = ""
    def_status: str = "untested"
    def_target_path: str = ""
    def_target_uri: str = ""
    def_target_line: int = 0
    def_target_char: int = 0
    stderr_tail: list[str] = field(default_factory=list)
    depth: int = 0

    @property
    def is_crash(self):
        return self.hover_status == "crash" or self.def_status == "crash"

    @property
    def is_timeout(self):
        return (self.hover_status == "timeout" or self.def_status == "timeout") and not self.is_crash

    @property
    def is_cross_file_def(self):
        return (self.def_status == "ok" and self.def_target_path and
                Path(self.def_target_path).resolve() != Path(self.file_path).resolve())

    def pos_str(self):
        return f"{relpath(self.file_path)}:{self.line + 1}:{self.char + 1}"

    def to_log_dict(self) -> dict:
        return {
            "type": "result",
            "timestamp": now_iso(),
            "file": self.file_path,
            "line": self.line + 1,
            "char": self.char + 1,
            "name": self.name,
            "depth": self.depth,
            "hover_status": self.hover_status,
            "hover_text": self.hover_text[:100] if self.hover_text else "",
            "def_status": self.def_status,
            "def_target": self.def_target_path,
            "def_target_line": self.def_target_line + 1,
            "stderr": self.stderr_tail,
        }


# ── Log file writer ───────────────────────────────────────────────────────────

class LogWriter:
    """Writes JSON-Lines to a log file, flushing after each entry."""

    def __init__(self, path: Optional[str]):
        self._f = None
        if path:
            try:
                self._f = open(path, "a", encoding="utf-8")
            except OSError as e:
                log.warning("Cannot open log file %s: %s", path, e)

    def write(self, obj: dict):
        if self._f:
            try:
                self._f.write(json.dumps(obj, ensure_ascii=False) + "\n")
                self._f.flush()
            except OSError:
                pass

    def close(self):
        if self._f:
            self._f.close()


def load_done_files(log_path: str) -> set[str]:
    """Return set of file paths already completed in a prior log."""
    done = set()
    try:
        with open(log_path, encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                try:
                    obj = json.loads(line)
                    if obj.get("type") == "file_done":
                        done.add(obj.get("file", ""))
                except json.JSONDecodeError:
                    pass
    except FileNotFoundError:
        pass
    return done


# ── Core tester ───────────────────────────────────────────────────────────────

class Tester:
    def __init__(
        self,
        binary: str,
        workspace: str,
        env: dict,
        max_depth: int = 2,
        positions_seed: int = 40,
        positions_follow: int = 15,
        timeout: float = 12.0,
    ):
        self.binary = binary
        self.workspace = workspace
        self.env = env
        self.max_depth = max_depth
        self.positions_seed = positions_seed
        self.positions_follow = positions_follow
        self.timeout = timeout

        self.results: list[TestResult] = []
        self._visited: set[tuple[str, int, int]] = set()
        self._proc: Optional[LspProcess] = None
        self._session: Optional[LspSession] = None
        self.restarts: int = 0

    # ── Lifecycle ─────────────────────────────────────────────────────────────

    def _start(self) -> bool:
        proc = LspProcess(self.binary, self.env, self.timeout)
        if not proc.start():
            return False
        session = LspSession(proc, self.workspace)
        if not session.initialize():
            proc.stop()
            return False
        self._proc = proc
        self._session = session
        return True

    def _restart(self, reopen: Optional[str] = None) -> bool:
        self.restarts += 1
        log.warning("  ↻ Restarting LSP (restart #%d)…", self.restarts)
        if self._proc:
            self._proc.stop()
        # New session: clear opened-docs tracking but keep visited set
        ok = self._start()
        if ok and reopen:
            self._session.open_document(reopen)
        return ok

    def _ensure_live(self, reopen: Optional[str] = None) -> bool:
        if self._proc and self._proc.is_alive():
            return True
        return self._restart(reopen)

    # ── Single-file run ───────────────────────────────────────────────────────

    def run(self, seed_file: str, specific_position: Optional[tuple[int, int]] = None):
        if not self._start():
            log.error("Cannot start LSP — aborting.")
            return
        try:
            if specific_position:
                line, char = specific_position
                name = _ident_at(seed_file, line, char)
                self._test_file(str(Path(seed_file).resolve()), 0, [(line, char, name)])
            else:
                self._test_file(str(Path(seed_file).resolve()), 0)
        finally:
            if self._proc:
                self._proc.stop()

    # ── Batch run ─────────────────────────────────────────────────────────────

    def run_batch(
        self,
        seed_files: list[str],
        log_writer: Optional[LogWriter] = None,
        skip_files: Optional[set[str]] = None,
        progress_interval: int = 10,
    ):
        if not self._start():
            log.error("Cannot start LSP — aborting batch.")
            return

        skip = skip_files or set()
        total = len(seed_files)

        if log_writer:
            log_writer.write({
                "type": "batch_start",
                "timestamp": now_iso(),
                "total_files": total,
                "depth": self.max_depth,
                "positions_seed": self.positions_seed,
                "positions_follow": self.positions_follow,
            })

        crashes_so_far = 0
        try:
            for idx, seed in enumerate(seed_files):
                abs_seed = str(Path(seed).resolve())

                if abs_seed in skip:
                    log.info("[%d/%d] SKIP (already done) %s", idx + 1, total, relpath(abs_seed))
                    continue

                if not Path(abs_seed).exists():
                    log.warning("[%d/%d] NOT FOUND: %s", idx + 1, total, abs_seed)
                    continue

                log.info("[%d/%d] %s", idx + 1, total, relpath(abs_seed))

                if not self._ensure_live(abs_seed):
                    log.error("LSP unavailable — skipping %s", relpath(abs_seed))
                    continue

                before = len(self.results)
                try:
                    self._test_file(abs_seed, depth=0)
                except Exception as e:
                    log.error("Unhandled error in %s: %s", relpath(abs_seed), e)

                file_results = self.results[before:]
                file_crashes = sum(1 for r in file_results if r.is_crash)
                crashes_so_far += file_crashes

                if log_writer:
                    for r in file_results:
                        log_writer.write(r.to_log_dict())
                    log_writer.write({
                        "type": "file_done",
                        "timestamp": now_iso(),
                        "file": abs_seed,
                        "positions": len(file_results),
                        "crashes": file_crashes,
                    })

                if (idx + 1) % progress_interval == 0 or file_crashes > 0:
                    total_so_far = len(self.results)
                    hover_ok = sum(1 for r in self.results if r.hover_status == "ok")
                    log.info(
                        "  ── progress: %d/%d files | %d positions | %d crashes | "
                        "%d hover-OK ──",
                        idx + 1, total, total_so_far, crashes_so_far, hover_ok,
                    )

        finally:
            if self._proc:
                self._proc.stop()
            if log_writer:
                log_writer.write({
                    "type": "batch_end",
                    "timestamp": now_iso(),
                    "files_done": len({r.file_path for r in self.results}),
                    "total_positions": len(self.results),
                    "crashes": sum(1 for r in self.results if r.is_crash),
                    "restarts": self.restarts,
                })

    # ── File-level testing ────────────────────────────────────────────────────

    def _test_file(
        self,
        abs_path: str,
        depth: int,
        positions: Optional[list[tuple[int, int, str]]] = None,
    ):
        if not self._ensure_live(abs_path):
            return
        if not self._session.open_document(abs_path):
            return

        if positions is None:
            try:
                text = Path(abs_path).read_text(errors="replace")
            except OSError:
                return
            budget = self.positions_seed if depth == 0 else self.positions_follow
            positions = scan_identifiers(text, budget)

        if not positions:
            return

        log.info("   depth=%d  %s  (%d positions)", depth, relpath(abs_path), len(positions))

        follow: dict[str, list[tuple[int, int, str]]] = {}

        for line, char, name in positions:
            key = (abs_path, line, char)
            if key in self._visited:
                continue
            self._visited.add(key)

            result = self._test_one(abs_path, line, char, name, depth)
            self.results.append(result)

            if result.is_cross_file_def and depth < self.max_depth:
                tp = result.def_target_path
                tk = (tp, result.def_target_line, result.def_target_char)
                if tk not in self._visited and Path(tp).exists():
                    if tp not in follow:
                        follow[tp] = []
                    entry = (result.def_target_line, result.def_target_char, name)
                    if entry not in follow[tp]:
                        follow[tp].insert(0, entry)

        for tp, tp_positions in follow.items():
            # Add auto-scanned positions from the target file
            try:
                text = Path(tp).read_text(errors="replace")
                auto = scan_identifiers(text, self.positions_follow)
                seen_keys = {(p[0], p[1]) for p in tp_positions}
                for p in auto:
                    if (p[0], p[1]) not in seen_keys:
                        tp_positions.append(p)
                        seen_keys.add((p[0], p[1]))
            except OSError:
                pass
            self._test_file(tp, depth + 1, tp_positions)

    # ── Position-level testing ────────────────────────────────────────────────

    def _test_one(self, file_path: str, line: int, char: int, name: str, depth: int) -> TestResult:
        r = TestResult(file_path=file_path, line=line, char=char, name=name, depth=depth)

        if not self._ensure_live(file_path):
            r.hover_status = r.def_status = "crash"
            self._emit(r)
            return r

        h_status, h_text = self._session.hover(file_path, line, char)
        if h_status == "crash" or (h_status != "timeout" and not self._proc.is_alive()):
            r.hover_status = "crash"
            r.stderr_tail = self._proc.recent_stderr() if self._proc else []
            log.warning("  💥 CRASH (hover) at %s (%s)", r.pos_str(), name)
            self._restart(file_path)
            r.def_status = "crash"
            self._emit(r)
            return r

        r.hover_status = h_status
        r.hover_text = h_text or ""

        if not self._ensure_live(file_path):
            r.def_status = "crash"
            self._emit(r)
            return r

        d_status, d_loc = self._session.definition(file_path, line, char)
        if d_status == "crash" or (d_status != "timeout" and not self._proc.is_alive()):
            r.def_status = "crash"
            r.stderr_tail = self._proc.recent_stderr() if self._proc else []
            log.warning("  💥 CRASH (definition) at %s (%s)", r.pos_str(), name)
            self._restart(file_path)
            self._emit(r)
            return r

        r.def_status = d_status
        if d_loc:
            r.def_target_uri = d_loc.get("uri", "")
            r.def_target_path = d_loc.get("path", "")
            r.def_target_line = d_loc.get("line", 0)
            r.def_target_char = d_loc.get("character", 0)

        self._emit(r)
        return r

    def _emit(self, r: TestResult):
        h = SYM.get(r.hover_status, "?")
        d = SYM.get(r.def_status, "?")
        target = ""
        if r.def_status == "ok" and r.def_target_path:
            target = f" → {relpath(r.def_target_path)}:{r.def_target_line + 1}"
            if r.is_cross_file_def:
                target += "  [✈]"
        detail = ""
        if r.hover_status == "ok" and r.hover_text:
            detail = f"  [{r.hover_text.splitlines()[0][:55]}]"
        log.debug(
            "    %-26s  h=%s d=%s%s%s",
            f"{name_trunc(r.name)}@{r.line+1}:{r.char+1}", h, d, detail, target,
        )
        if r.is_crash or r.is_timeout:
            log.info(
                "    %-26s  h=%s d=%s%s%s",
                f"{name_trunc(r.name)}@{r.line+1}:{r.char+1}", h, d, detail, target,
            )


def name_trunc(name: str, n: int = 22) -> str:
    return name[:n] + "…" if len(name) > n else name


def _ident_at(file_path: str, line: int, char: int) -> str:
    try:
        lines = Path(file_path).read_text(errors="replace").splitlines()
        if line < len(lines):
            m = _IDENT_RE.search(lines[line], char)
            if m and m.start() == char:
                return m.group()
    except OSError:
        pass
    return ""


# ── Report ────────────────────────────────────────────────────────────────────

def print_report(results: list[TestResult], restarts: int, json_path: Optional[str] = None) -> int:
    crashes = [r for r in results if r.is_crash]
    timeouts = [r for r in results if r.is_timeout]
    cross = [r for r in results if r.is_cross_file_def]
    hover_ok = sum(1 for r in results if r.hover_status == "ok")
    def_ok = sum(1 for r in results if r.def_status == "ok")
    files_tested = len({r.file_path for r in results})

    w = 72
    bar, thin = "═" * w, "─" * w

    print(f"\n{bar}")
    print("  lsp-tester report")
    print(bar)
    print(f"  Files tested      : {files_tested}")
    print(f"  Positions tested  : {len(results)}")
    print(f"  Server restarts   : {restarts}")
    print(f"  Hover OK          : {hover_ok}/{len(results)}")
    print(f"  Definition OK     : {def_ok}/{len(results)}")
    print(f"  Cross-file defs   : {len(cross)}")
    print(f"  Timeouts          : {len(timeouts)}")
    print(f"  CRASHES           : {len(crashes)}")
    print()

    if crashes:
        print(f"  {thin}")
        print("  CRASHES")
        print(f"  {thin}")
        for r in crashes:
            which = [s for s in ("hover", "definition")
                     if getattr(r, f"{s.replace('-','_').split()[0]}_status") == "crash"]
            print(f"  {r.pos_str()}  ({r.name})  [{', '.join(which)}]")
            for ln in r.stderr_tail[-5:]:
                print(f"      stderr▸  {ln}")
        print()

    if timeouts:
        print(f"  {thin}")
        print("  TIMEOUTS")
        print(f"  {thin}")
        for r in timeouts:
            which = [s for s in ("hover", "definition")
                     if getattr(r, f"{s.replace('-','_').split()[0]}_status") == "timeout"]
            print(f"  {r.pos_str()}  ({r.name})  [{', '.join(which)}]")
        print()

    if cross:
        print(f"  {thin}")
        print(f"  CROSS-FILE DEFINITIONS ({len(cross)} total)")
        print(f"  {thin}")
        # Group by target file
        by_target: dict[str, list[TestResult]] = {}
        for r in cross:
            t = relpath(r.def_target_path)
            by_target.setdefault(t, []).append(r)
        for tgt, rs in sorted(by_target.items()):
            print(f"  → {tgt}  ({len(rs)} references)")
            for r in rs[:3]:
                print(f"      from {r.pos_str()}  ({r.name})")
            if len(rs) > 3:
                print(f"      … and {len(rs)-3} more")
        print()

    print(bar)

    if json_path:
        data = {
            "summary": {
                "files_tested": files_tested, "total": len(results),
                "restarts": restarts, "hover_ok": hover_ok, "def_ok": def_ok,
                "cross_file_defs": len(cross), "timeouts": len(timeouts),
                "crashes": len(crashes),
            },
            "crashes": [
                {"position": r.pos_str(), "name": r.name,
                 "hover_status": r.hover_status, "def_status": r.def_status,
                 "depth": r.depth, "stderr": r.stderr_tail}
                for r in crashes
            ],
            "timeouts": [
                {"position": r.pos_str(), "name": r.name,
                 "hover_status": r.hover_status, "def_status": r.def_status,
                 "depth": r.depth}
                for r in timeouts
            ],
            "cross_file_defs": [
                {"source": r.pos_str(), "name": r.name,
                 "target_path": r.def_target_path, "target_line": r.def_target_line + 1}
                for r in cross
            ],
            "all_results": [
                {"position": r.pos_str(), "name": r.name, "depth": r.depth,
                 "hover_status": r.hover_status,
                 "hover_text": r.hover_text[:120] if r.hover_text else "",
                 "def_status": r.def_status,
                 "def_target": (f"{relpath(r.def_target_path)}:{r.def_target_line+1}"
                                if r.def_target_path else "")}
                for r in results
            ],
        }
        try:
            with open(json_path, "w") as f:
                json.dump(data, f, indent=2)
            print(f"  JSON summary → {json_path}")
        except OSError as e:
            log.warning("Could not write JSON: %s", e)

    return EXIT_OK if not crashes else EXIT_CRASHES


# ── File discovery ────────────────────────────────────────────────────────────

_PRUNE_DIRS = frozenset({
    "dist-newstyle", "dist", ".stack-work", ".git", "node_modules",
    "_build", "build", "__pycache__", ".cabal",
})

def collect_source_files(dirs: list[str], exts: tuple[str, ...] = (".bs", ".bsv")) -> list[str]:
    """Recursively find all .bs/.bsv files, skipping build/vcs directories."""
    files = []
    for root_dir in dirs:
        root = Path(root_dir).resolve()
        if not root.exists():
            log.warning("Directory not found: %s", root_dir)
            continue
        for dirpath, dirnames, filenames in os.walk(root):
            # Prune build/vcs directories in-place
            dirnames[:] = [d for d in dirnames if d not in _PRUNE_DIRS]
            for fname in filenames:
                if any(fname.endswith(e) for e in exts):
                    files.append(str(Path(dirpath) / fname))
    return sorted(files)


# ── Binary / workspace discovery ─────────────────────────────────────────────

def find_lsp_binary() -> Optional[str]:
    import shutil
    found = shutil.which("bs-lsp")
    if found:
        return found
    here = Path(__file__).resolve().parent.parent  # util/lsp/
    candidate = here / "bs-lsp-bin"
    if candidate.is_file() and os.access(candidate, os.X_OK):
        return str(candidate)
    cabal_root = here / "bs-lsp"
    if cabal_root.is_dir():
        for p in cabal_root.rglob("bs-lsp"):
            if p.is_file() and os.access(p, os.X_OK) and "build/bs-lsp/bs-lsp" in str(p):
                return str(p)
    return None

def find_workspace_root(file_path: str) -> str:
    p = Path(file_path).resolve().parent
    for ancestor in [p, *p.parents]:
        if (ancestor / ".git").exists():
            return str(ancestor)
        if (ancestor / "BUILD").exists() or (ancestor / "WORKSPACE").exists():
            return str(ancestor)
    return str(p)


# ── CLI ───────────────────────────────────────────────────────────────────────

def main() -> int:
    ap = argparse.ArgumentParser(
        description="Automated LSP integration tester for bs-lsp.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=(
            "Single-file:\n"
            "  python3 lsp_tester.py TV_Info.bsv\n"
            "  python3 lsp_tester.py TV_Info.bsv --position 352:14\n\n"
            "Batch (all .bs/.bsv files in directories, one shared LSP session):\n"
            "  python3 lsp_tester.py --dirs /work/Flute /work/Toooba /work/Piccolo\n"
            "      --bluespec-src /work/bsc --log /tmp/scan.jsonl --json /tmp/summary.json\n\n"
            "Resume an interrupted batch:\n"
            "  python3 lsp_tester.py --dirs /work/Flute --log /tmp/scan.jsonl --resume\n\n"
            "Exit codes: 0=no crashes, 1=crashes, 2=tool error"
        ),
    )
    ap.add_argument("files", nargs="*", help="Seed BSV/BS file(s) to test")
    ap.add_argument("--dirs", nargs="+", metavar="DIR", default=[],
                    help="Scan directories for all .bs/.bsv files (batch mode)")
    ap.add_argument("--lsp", default=None, metavar="PATH",
                    help="Path to bs-lsp binary (default: auto-detect)")
    ap.add_argument("--workspace", default=None, metavar="DIR",
                    help="Workspace root for LSP initialization")
    ap.add_argument("--depth", type=int, default=2, metavar="N",
                    help="Cross-file definition follow depth (default: 2)")
    ap.add_argument("--positions", type=int, default=40, metavar="N",
                    help="Max identifiers per seed file (default: 40)")
    ap.add_argument("--follow-positions", type=int, default=15, metavar="N",
                    help="Max identifiers per followed file (default: 15)")
    ap.add_argument("--timeout", type=float, default=12.0, metavar="SECS",
                    help="Per-request timeout in seconds (default: 12)")
    ap.add_argument("--position", default=None, metavar="LINE:COL",
                    help="Single-file mode: test only this 1-indexed position")
    ap.add_argument("--bluespec-src", default=None, metavar="DIR",
                    help="Set BLUESPEC_SRC env var for the server")
    ap.add_argument("--bluespecdir", default=None, metavar="DIR",
                    help="Set BLUESPECDIR env var for the server")
    ap.add_argument("--log", default=None, metavar="FILE",
                    help="Append JSON-Lines progress to FILE (incremental; survives crashes)")
    ap.add_argument("--resume", action="store_true",
                    help="With --log: skip files already recorded as done in the log")
    ap.add_argument("--json", default=None, metavar="FILE",
                    help="Write final JSON summary to FILE")
    ap.add_argument("--progress-interval", type=int, default=10, metavar="N",
                    help="Print running totals every N files in batch mode (default: 10)")
    ap.add_argument("--verbose", "-v", action="store_true",
                    help="Print every position result (default: crashes/timeouts only)")
    ap.add_argument("--max-files", type=int, default=0, metavar="N",
                    help="Stop after testing N files (0=unlimited; useful for dry runs)")
    args = ap.parse_args()

    logging.basicConfig(
        level=logging.DEBUG if args.verbose else logging.INFO,
        format="%(message)s", stream=sys.stderr,
    )

    # ── Collect file list ──────────────────────────────────────────────────────
    explicit = [str(Path(f).resolve()) for f in args.files]
    dir_files = collect_source_files(args.dirs) if args.dirs else []
    all_files = explicit + [f for f in dir_files if f not in set(explicit)]

    if not all_files:
        print("Error: no files specified. Use FILE arguments or --dirs.", file=sys.stderr)
        return EXIT_TOOL_ERROR

    if args.max_files > 0:
        all_files = all_files[:args.max_files]

    # ── Validate inputs ───────────────────────────────────────────────────────
    binary = args.lsp or find_lsp_binary()
    if not binary or not Path(binary).exists():
        print(
            "Error: bs-lsp not found.\n"
            "Build with:  cd util/lsp && make\n"
            "or pass:     --lsp /path/to/bs-lsp",
            file=sys.stderr,
        )
        return EXIT_TOOL_ERROR
    if not os.access(binary, os.X_OK):
        print(f"Error: {binary} is not executable", file=sys.stderr)
        return EXIT_TOOL_ERROR

    # ── Workspace root ────────────────────────────────────────────────────────
    if args.workspace:
        workspace = args.workspace
    elif args.dirs:
        # For multi-dir batch, use the nearest common ancestor or first dir's root
        workspace = find_workspace_root(all_files[0]) if all_files else args.dirs[0]
    else:
        workspace = find_workspace_root(all_files[0])

    # ── Environment ───────────────────────────────────────────────────────────
    env = os.environ.copy()
    if args.bluespec_src:
        env["BLUESPEC_SRC"] = args.bluespec_src
    if args.bluespecdir:
        env["BLUESPECDIR"] = args.bluespecdir

    # ── Parse --position ──────────────────────────────────────────────────────
    specific_pos: Optional[tuple[int, int]] = None
    if args.position:
        try:
            parts = args.position.split(":")
            specific_pos = (int(parts[0]) - 1, int(parts[1]) - 1)
        except (ValueError, IndexError):
            print(f"Error: --position must be LINE:COL (1-indexed), got: {args.position}",
                  file=sys.stderr)
            return EXIT_TOOL_ERROR

    # ── Banner ────────────────────────────────────────────────────────────────
    batch_mode = bool(args.dirs) or len(all_files) > 1

    log.info("bs-lsp      : %s", binary)
    log.info("workspace   : %s", workspace)
    log.info("depth       : %d", args.depth)
    if batch_mode:
        log.info("files       : %d total", len(all_files))
    else:
        log.info("seed file   : %s", relpath(all_files[0]))
    if args.bluespec_src:
        log.info("BLUESPEC_SRC: %s", args.bluespec_src)
    if args.log:
        log.info("log file    : %s", args.log)
    log.info("")

    # ── Build tester ──────────────────────────────────────────────────────────
    tester = Tester(
        binary=binary, workspace=workspace, env=env,
        max_depth=args.depth,
        positions_seed=args.positions,
        positions_follow=args.follow_positions,
        timeout=args.timeout,
    )

    # ── Run ───────────────────────────────────────────────────────────────────
    log_writer = LogWriter(args.log)
    skip_files: set[str] = set()
    if args.resume and args.log:
        skip_files = {str(Path(f).resolve()) for f in load_done_files(args.log)}
        if skip_files:
            log.info("Resuming: skipping %d already-done files", len(skip_files))

    try:
        if batch_mode:
            tester.run_batch(
                all_files,
                log_writer=log_writer,
                skip_files=skip_files,
                progress_interval=args.progress_interval,
            )
        else:
            tester.run(all_files[0], specific_position=specific_pos)
    finally:
        log_writer.close()

    rc = print_report(tester.results, tester.restarts, json_path=args.json)
    return rc


if __name__ == "__main__":
    sys.exit(main())
