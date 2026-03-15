#!/usr/bin/env python3
"""
lsp-tester — integration test harness for bs-lsp.

Starts bs-lsp, opens a BSV/BS source file, and systematically tests
textDocument/hover (type inference) and textDocument/definition (go-to-def)
for sampled identifier positions.  Follows definitions across file boundaries
(into stdlib, Prelude, etc.) up to a configurable depth, specifically watching
for server **crashes** — the primary failure mode in cross-file navigation.

Exit codes:
  0  No crashes detected
  1  One or more crashes detected
  2  Tool error (binary not found, file unreadable, LSP won't start, etc.)

Usage:
  python3 lsp_tester.py [OPTIONS] FILE.bsv
  python3 lsp_tester.py --help
"""

import argparse
import json
import logging
import os
import re
import select
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
SYM = {
    "ok": "✓",
    "null": "·",
    "crash": "💥",
    "timeout": "⏱",
    "error": "!",
    "skip": "~",
}

log = logging.getLogger("lsp-tester")


# ── URI helpers ───────────────────────────────────────────────────────────────

def uri_to_path(uri: str) -> str:
    """Convert a file:// URI to an absolute path."""
    parsed = urlparse(uri)
    return unquote(parsed.path)


def path_to_uri(path: str) -> str:
    """Convert an absolute path to a file:// URI."""
    return Path(path).resolve().as_uri()


def relpath(path: str) -> str:
    """Return path relative to cwd, or absolute if that fails."""
    try:
        return str(Path(path).relative_to(Path.cwd()))
    except ValueError:
        return path


# ── JSON-RPC framing ──────────────────────────────────────────────────────────

def _encode(obj: dict) -> bytes:
    body = json.dumps(obj, separators=(",", ":")).encode("utf-8")
    return f"Content-Length: {len(body)}\r\n\r\n".encode() + body


class _MessageBuffer:
    """Incremental parser for LSP JSON-RPC message stream."""

    def __init__(self):
        self._buf = b""

    def feed(self, data: bytes) -> list[dict]:
        self._buf += data
        msgs = []
        while True:
            # Find end of headers (blank line)
            idx = self._buf.find(b"\r\n\r\n")
            if idx == -1:
                break
            header_block = self._buf[:idx]
            m = re.search(rb"Content-Length:\s*(\d+)", header_block, re.IGNORECASE)
            if not m:
                # Malformed — skip to next potential message
                self._buf = self._buf[idx + 4:]
                continue
            length = int(m.group(1))
            body_start = idx + 4
            body_end = body_start + length
            if len(self._buf) < body_end:
                break  # need more data
            body = self._buf[body_start:body_end]
            self._buf = self._buf[body_end:]
            try:
                msgs.append(json.loads(body))
            except json.JSONDecodeError as e:
                log.debug("JSON decode error: %s", e)
        return msgs


# ── LSP process wrapper ───────────────────────────────────────────────────────

class LspProcess:
    """Manages a bs-lsp subprocess and its JSON-RPC communication.

    A background thread reads all stdout output and feeds a Queue.
    A second background thread drains stderr into a capped deque.
    The main thread sends requests and polls the queue for responses.
    """

    def __init__(self, binary: str, env: dict, request_timeout: float = 10.0):
        self.binary = binary
        self.env = env
        self.request_timeout = request_timeout

        self._proc: Optional[subprocess.Popen] = None
        self._msg_q: Queue = Queue()
        self._pending_q: Queue = Queue()      # for out-of-order responses
        self._req_id = 0
        self._id_lock = threading.Lock()
        self._stderr_buf: deque = deque(maxlen=300)
        self._started = False

    def start(self) -> bool:
        try:
            self._proc = subprocess.Popen(
                [self.binary],
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                env=self.env,
                bufsize=0,
            )
        except (FileNotFoundError, PermissionError, OSError) as e:
            log.error("Cannot start %s: %s", self.binary, e)
            return False

        threading.Thread(target=self._read_stdout, daemon=True).start()
        threading.Thread(target=self._read_stderr, daemon=True).start()
        self._started = True
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

    def exit_code(self) -> Optional[int]:
        return self._proc.poll() if self._proc else None

    def recent_stderr(self, n: int = 25) -> list[str]:
        return list(self._stderr_buf)[-n:]

    def _next_id(self) -> int:
        with self._id_lock:
            self._req_id += 1
            return self._req_id

    def notify(self, method: str, params) -> bool:
        if not self.is_alive():
            return False
        try:
            data = _encode({"jsonrpc": "2.0", "method": method, "params": params})
            self._proc.stdin.write(data)
            self._proc.stdin.flush()
            return True
        except (BrokenPipeError, OSError):
            return False

    def request(self, method: str, params) -> Optional[dict]:
        """Send a request and wait for its response.  Returns None on crash or timeout."""
        req_id = self._next_id()
        msg = {"jsonrpc": "2.0", "id": req_id, "method": method, "params": params}
        if not self.is_alive():
            return None
        try:
            self._proc.stdin.write(_encode(msg))
            self._proc.stdin.flush()
        except (BrokenPipeError, OSError):
            return None

        deadline = time.monotonic() + self.request_timeout
        while time.monotonic() < deadline:
            if not self.is_alive():
                return None  # crashed while waiting
            try:
                resp = self._msg_q.get(timeout=0.15)
            except Empty:
                continue
            # Notifications have a "method" key and no numeric "id".
            if "method" in resp and "id" not in resp:
                continue  # skip server notifications
            if resp.get("id") == req_id:
                return resp
            # Wrong id (stale or out-of-order) — skip it
        return None  # timeout

    def stop(self):
        if not self.is_alive():
            return
        try:
            self.request("shutdown", None)
            self.notify("exit", None)
            self._proc.wait(timeout=3)
        except Exception:
            pass
        if self.is_alive():
            try:
                self._proc.kill()
            except Exception:
                pass


# ── LSP session (protocol-level) ─────────────────────────────────────────────

class LspSession:
    """Manages the LSP handshake and document lifecycle."""

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
            "workspaceFolders": [
                {"uri": path_to_uri(self.workspace), "name": Path(self.workspace).name}
            ],
        })
        if resp is None or "error" in resp:
            log.error("initialize failed: %s", resp)
            return False
        self.proc.notify("initialized", {})
        time.sleep(0.3)  # let server boot background indexing
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
        lang_id = "bluespec" if ext == ".bs" else "bluespec-sv"
        ok = self.proc.notify("textDocument/didOpen", {
            "textDocument": {
                "uri": path_to_uri(abs_path),
                "languageId": lang_id,
                "version": 1,
                "text": text,
            }
        })
        if ok:
            self._open_docs.add(abs_path)
            # Brief pause — the server parses asynchronously, but hover/definition
            # will still be handled once queued; this just reduces spurious nulls.
            time.sleep(0.15)
        return ok

    def hover(self, file_path: str, line: int, char: int) -> tuple[str, Optional[str]]:
        """
        Returns (status, text) where status is one of:
          "ok", "null", "crash", "timeout", "error"
        """
        abs_path = str(Path(file_path).resolve())
        resp = self.proc.request("textDocument/hover", {
            "textDocument": {"uri": path_to_uri(abs_path)},
            "position": {"line": line, "character": char},
        })
        return self._decode_hover(resp)

    def definition(
        self, file_path: str, line: int, char: int
    ) -> tuple[str, Optional[dict]]:
        """
        Returns (status, location_dict_or_None) where status is one of:
          "ok", "null", "crash", "timeout", "error"
        location_dict has keys: uri, line (0-indexed), character (0-indexed)
        """
        abs_path = str(Path(file_path).resolve())
        resp = self.proc.request("textDocument/definition", {
            "textDocument": {"uri": path_to_uri(abs_path)},
            "position": {"line": line, "character": char},
        })
        return self._decode_definition(resp)

    # ── response decoders ─────────────────────────────────────────────────────

    def _decode_hover(self, resp: Optional[dict]) -> tuple[str, Optional[str]]:
        if resp is None:
            status = "crash" if not self.proc.is_alive() else "timeout"
            return status, None
        if "error" in resp:
            return "error", str(resp["error"])
        result = resp.get("result")
        if result is None:
            return "null", None
        # result = Hover: {"contents": {"kind": "markdown", "value": "..."}, "range": ...}
        contents = result.get("contents", "")
        if isinstance(contents, dict):
            text = contents.get("value", "")
        elif isinstance(contents, list):
            text = " | ".join(
                (c.get("value", "") if isinstance(c, dict) else str(c))
                for c in contents
            )
        else:
            text = str(contents)
        if not text.strip():
            return "null", None
        return "ok", text.strip()

    def _decode_definition(
        self, resp: Optional[dict]
    ) -> tuple[str, Optional[dict]]:
        if resp is None:
            status = "crash" if not self.proc.is_alive() else "timeout"
            return status, None
        if "error" in resp:
            return "error", None
        result = resp.get("result")
        if result is None:
            return "null", None
        # result may be a single Location, a list of LocationLinks, or null
        if isinstance(result, list):
            result = result[0] if result else None
        if not result or not isinstance(result, dict):
            return "null", None
        uri = result.get("uri", "")
        rng = result.get("range", {})
        start = rng.get("start", {})
        loc = {
            "uri": uri,
            "path": uri_to_path(uri),
            "line": start.get("line", 0),
            "character": start.get("character", 0),
        }
        return "ok", loc


# ── Identifier scanning ───────────────────────────────────────────────────────

# Bluespec structural/noise keywords that produce boring hover results
_SKIP_WORDS = frozenset({
    "module", "endmodule", "interface", "endinterface", "method", "endmethod",
    "rule", "endrule", "action", "endaction", "actionvalue", "endactionvalue",
    "function", "endfunction", "package", "endpackage", "instance", "endinstance",
    "typeclass", "endtypeclass", "if", "else", "begin", "end", "case", "endcase",
    "of", "let", "in", "where", "do", "return", "import", "export", "type",
    "typedef", "struct", "enum", "union", "tagged", "deriving", "provisos",
    "for", "while", "seq", "endseq", "par", "endpar", "match", "matches",
    "numeric", "void", "Bool", "True", "False",
})

_IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
_LINE_COMMENT_RE = re.compile(r"//.*$")
_BLOCK_COMMENT_RE = re.compile(r"/\*.*?\*/", re.DOTALL)
_STRING_LIT_RE = re.compile(r'"[^"\\]*(?:\\.[^"\\]*)*"')


def scan_identifiers(
    text: str, max_count: int = 50
) -> list[tuple[int, int, str]]:
    """
    Return a reproducible sample of (line_0, char_0, name) tuples.
    Strips comments and string literals before scanning.
    Skips structural keywords.  Deduplicates by name (first occurrence kept).
    If there are more candidates than max_count, samples evenly across the file.
    """
    # Strip block comments, preserving newlines
    clean = _BLOCK_COMMENT_RE.sub(lambda m: "\n" * m.group().count("\n"), text)
    lines = clean.splitlines()

    candidates: list[tuple[int, int, str]] = []
    seen: set[str] = set()

    for lineno, line in enumerate(lines):
        # Strip line comment and string literals
        line_clean = _LINE_COMMENT_RE.sub("", line)
        line_clean = _STRING_LIT_RE.sub("", line_clean)
        for m in _IDENT_RE.finditer(line_clean):
            name = m.group()
            if name in _SKIP_WORDS:
                continue
            if name in seen:
                continue
            seen.add(name)
            candidates.append((lineno, m.start(), name))

    if len(candidates) <= max_count:
        return candidates

    # Evenly spaced sample for reproducibility
    step = len(candidates) / max_count
    return [candidates[int(i * step)] for i in range(max_count)]


# ── Result types ──────────────────────────────────────────────────────────────

@dataclass
class TestResult:
    file_path: str
    line: int       # 0-indexed
    char: int       # 0-indexed
    name: str       # identifier token at this position

    hover_status: str = "untested"   # ok | null | crash | timeout | error
    hover_text: str = ""

    def_status: str = "untested"     # ok | null | crash | timeout | error
    def_target_uri: str = ""
    def_target_path: str = ""
    def_target_line: int = 0
    def_target_char: int = 0

    stderr_tail: list[str] = field(default_factory=list)
    depth: int = 0

    @property
    def is_crash(self) -> bool:
        return self.hover_status == "crash" or self.def_status == "crash"

    @property
    def is_timeout(self) -> bool:
        return self.hover_status == "timeout" or self.def_status == "timeout"

    @property
    def is_cross_file_def(self) -> bool:
        return (
            self.def_status == "ok"
            and self.def_target_path
            and Path(self.def_target_path).resolve() != Path(self.file_path).resolve()
        )

    def pos_str(self) -> str:
        return f"{relpath(self.file_path)}:{self.line + 1}:{self.char + 1}"


# ── Core tester ───────────────────────────────────────────────────────────────

class Tester:
    def __init__(
        self,
        binary: str,
        workspace: str,
        env: dict,
        max_depth: int = 2,
        positions_seed: int = 50,
        positions_follow: int = 20,
        timeout: float = 10.0,
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
        self._restarts = 0

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

    def _restart(self, reopen_path: Optional[str] = None) -> bool:
        self._restarts += 1
        log.warning("↻  Restarting LSP (restart #%d)…", self._restarts)
        if self._proc:
            self._proc.stop()
        ok = self._start()
        if ok and reopen_path:
            self._session.open_document(reopen_path)
        return ok

    def _ensure_live(self, reopen_path: Optional[str] = None) -> bool:
        if self._proc and self._proc.is_alive():
            return True
        return self._restart(reopen_path)

    # ── Main entry point ──────────────────────────────────────────────────────

    def run(self, seed_file: str, specific_position: Optional[tuple[int, int]] = None):
        if not self._start():
            log.error("Cannot start LSP — aborting.")
            return

        try:
            if specific_position:
                line, char = specific_position
                # Find the name at this position
                try:
                    text = Path(seed_file).read_text(errors="replace")
                    lines = text.splitlines()
                    name = ""
                    if line < len(lines):
                        m = _IDENT_RE.search(lines[line], char)
                        if m and m.start() == char:
                            name = m.group()
                except OSError:
                    name = ""
                self._test_file(
                    str(Path(seed_file).resolve()),
                    depth=0,
                    positions=[(line, char, name)],
                )
            else:
                self._test_file(
                    str(Path(seed_file).resolve()),
                    depth=0,
                    positions=None,  # auto-scan
                )
        finally:
            if self._proc:
                self._proc.stop()

    # ── File-level testing ────────────────────────────────────────────────────

    def _test_file(
        self,
        abs_path: str,
        depth: int,
        positions: Optional[list[tuple[int, int, str]]] = None,
    ):
        if not self._ensure_live(abs_path):
            log.error("LSP unavailable — skipping %s", relpath(abs_path))
            return

        if not self._session.open_document(abs_path):
            log.warning("Cannot open %s — skipping", relpath(abs_path))
            return

        if positions is None:
            try:
                text = Path(abs_path).read_text(errors="replace")
            except OSError:
                return
            max_pos = self.positions_seed if depth == 0 else self.positions_follow
            positions = scan_identifiers(text, max_pos)

        log.info(
            "\n── depth=%d  %s  (%d positions) ──",
            depth, relpath(abs_path), len(positions),
        )

        follow_set: dict[str, list[tuple[int, int, str]]] = {}  # path → positions

        for line, char, name in positions:
            key = (abs_path, line, char)
            if key in self._visited:
                continue
            self._visited.add(key)

            result = self._test_one(abs_path, line, char, name, depth)
            self.results.append(result)

            # Collect cross-file targets to follow at next depth
            if result.is_cross_file_def and depth < self.max_depth:
                tgt_path = result.def_target_path
                tgt_key = (tgt_path, result.def_target_line, result.def_target_char)
                if tgt_key not in self._visited and Path(tgt_path).exists():
                    if tgt_path not in follow_set:
                        follow_set[tgt_path] = []
                    # Prepend the exact destination so it's always tested
                    if (result.def_target_line, result.def_target_char, name) \
                            not in follow_set[tgt_path]:
                        follow_set[tgt_path].insert(
                            0,
                            (result.def_target_line, result.def_target_char, name),
                        )

        # Follow cross-file definitions at depth+1
        for tgt_path, tgt_positions in follow_set.items():
            # Add auto-scanned positions too (limited budget)
            try:
                text = Path(tgt_path).read_text(errors="replace")
                auto = scan_identifiers(text, self.positions_follow)
                # Combine: exact targets first, then auto (dedup by key)
                seen_keys: set[tuple[int, int]] = {(p[0], p[1]) for p in tgt_positions}
                for p in auto:
                    if (p[0], p[1]) not in seen_keys:
                        tgt_positions.append(p)
                        seen_keys.add((p[0], p[1]))
            except OSError:
                pass
            self._test_file(tgt_path, depth + 1, tgt_positions)

    # ── Position-level testing ────────────────────────────────────────────────

    def _test_one(
        self, file_path: str, line: int, char: int, name: str, depth: int
    ) -> TestResult:
        result = TestResult(
            file_path=file_path, line=line, char=char, name=name, depth=depth
        )

        # ── Hover ─────────────────────────────────────────────────────────────
        if not self._ensure_live(file_path):
            result.hover_status = "crash"
            result.def_status = "crash"
            result.stderr_tail = []
            self._emit_progress(result)
            return result

        h_status, h_text = self._session.hover(file_path, line, char)

        if h_status == "crash" or (
            h_status in ("crash", "timeout") and not self._proc.is_alive()
        ):
            result.hover_status = "crash"
            result.stderr_tail = self._proc.recent_stderr()
            log.warning(
                "💥 CRASH (hover) at %s (%s)", result.pos_str(), name
            )
            self._restart(file_path)
            result.def_status = "crash"
            self._emit_progress(result)
            return result

        result.hover_status = h_status
        result.hover_text = h_text or ""

        # ── Definition ────────────────────────────────────────────────────────
        if not self._ensure_live(file_path):
            result.def_status = "crash"
            result.stderr_tail = []
            self._emit_progress(result)
            return result

        d_status, d_loc = self._session.definition(file_path, line, char)

        if d_status == "crash" or (
            d_status in ("crash", "timeout") and not self._proc.is_alive()
        ):
            result.def_status = "crash"
            result.stderr_tail = self._proc.recent_stderr()
            log.warning(
                "💥 CRASH (definition) at %s (%s)", result.pos_str(), name
            )
            self._restart(file_path)
            self._emit_progress(result)
            return result

        result.def_status = d_status
        if d_loc:
            result.def_target_uri = d_loc.get("uri", "")
            result.def_target_path = d_loc.get("path", "")
            result.def_target_line = d_loc.get("line", 0)
            result.def_target_char = d_loc.get("character", 0)

        self._emit_progress(result)
        return result

    def _emit_progress(self, r: TestResult):
        h = SYM.get(r.hover_status, "?")
        d = SYM.get(r.def_status, "?")
        target = ""
        if r.def_status == "ok" and r.def_target_path:
            tgt_rel = relpath(r.def_target_path)
            target = f" → {tgt_rel}:{r.def_target_line + 1}:{r.def_target_char + 1}"
            if r.is_cross_file_def:
                target += "  [cross-file]"
        hover_detail = ""
        if r.hover_status == "ok" and r.hover_text:
            first_line = r.hover_text.splitlines()[0]
            hover_detail = f"  [{first_line[:60]}]"
        log.info(
            "  %-28s  hover=%s  def=%s%s%s",
            f"{r.name}@{r.line + 1}:{r.char + 1}",
            h, d,
            hover_detail,
            target,
        )


# ── Report ────────────────────────────────────────────────────────────────────

def print_report(
    results: list[TestResult],
    restarts: int,
    json_path: Optional[str] = None,
) -> int:
    crashes = [r for r in results if r.is_crash]
    timeouts = [r for r in results if r.is_timeout and not r.is_crash]
    cross = [r for r in results if r.is_cross_file_def]
    hover_ok = sum(1 for r in results if r.hover_status == "ok")
    def_ok = sum(1 for r in results if r.def_status == "ok")

    w = 72
    bar = "═" * w
    thin = "─" * w

    print(f"\n{bar}")
    print("  lsp-tester report")
    print(bar)
    print(f"  Positions tested  : {len(results)}")
    print(f"  Server restarts   : {restarts}")
    print(f"  Hover OK          : {hover_ok}")
    print(f"  Definition OK     : {def_ok}")
    print(f"  Cross-file defs   : {len(cross)}")
    print(f"  Timeouts          : {len(timeouts)}")
    print(f"  CRASHES           : {len(crashes)}")
    print()

    if crashes:
        print(f"  {thin}")
        print("  CRASHES")
        print(f"  {thin}")
        for r in crashes:
            which = []
            if r.hover_status == "crash":
                which.append("hover")
            if r.def_status == "crash":
                which.append("definition")
            print(f"  {r.pos_str()}  ({r.name})  [{', '.join(which)}]")
            for line in r.stderr_tail[-6:]:
                print(f"      stderr▸  {line}")
        print()

    if timeouts:
        print(f"  {thin}")
        print("  TIMEOUTS")
        print(f"  {thin}")
        for r in timeouts:
            which = []
            if r.hover_status == "timeout":
                which.append("hover")
            if r.def_status == "timeout":
                which.append("definition")
            print(f"  {r.pos_str()}  ({r.name})  [{', '.join(which)}]")
        print()

    if cross:
        print(f"  {thin}")
        print("  CROSS-FILE DEFINITIONS")
        print(f"  {thin}")
        for r in cross:
            src = r.pos_str()
            tgt = f"{relpath(r.def_target_path)}:{r.def_target_line + 1}"
            print(f"  {src}  {r.name}  →  {tgt}")
        print()

    print(bar)
    rc = EXIT_OK if not crashes else EXIT_CRASHES

    if json_path:
        data = {
            "summary": {
                "total": len(results),
                "restarts": restarts,
                "hover_ok": hover_ok,
                "def_ok": def_ok,
                "cross_file_defs": len(cross),
                "timeouts": len(timeouts),
                "crashes": len(crashes),
            },
            "crashes": [
                {
                    "position": r.pos_str(),
                    "name": r.name,
                    "hover_status": r.hover_status,
                    "def_status": r.def_status,
                    "depth": r.depth,
                    "stderr": r.stderr_tail,
                }
                for r in crashes
            ],
            "timeouts": [
                {
                    "position": r.pos_str(),
                    "name": r.name,
                    "hover_status": r.hover_status,
                    "def_status": r.def_status,
                    "depth": r.depth,
                }
                for r in timeouts
            ],
            "cross_file_defs": [
                {
                    "source": r.pos_str(),
                    "name": r.name,
                    "target_path": r.def_target_path,
                    "target_line": r.def_target_line + 1,
                }
                for r in cross
            ],
            "all_results": [
                {
                    "position": r.pos_str(),
                    "name": r.name,
                    "depth": r.depth,
                    "hover_status": r.hover_status,
                    "hover_text": r.hover_text[:120] if r.hover_text else "",
                    "def_status": r.def_status,
                    "def_target": (
                        f"{relpath(r.def_target_path)}:{r.def_target_line + 1}"
                        if r.def_target_path
                        else ""
                    ),
                }
                for r in results
            ],
        }
        try:
            with open(json_path, "w") as f:
                json.dump(data, f, indent=2)
            print(f"  JSON report → {json_path}")
        except OSError as e:
            log.warning("Could not write JSON report: %s", e)

    return rc


# ── Binary discovery ──────────────────────────────────────────────────────────

def find_lsp_binary() -> Optional[str]:
    """Locate the bs-lsp binary via PATH, then cabal dist, then util/lsp."""
    import shutil

    # 1. PATH
    found = shutil.which("bs-lsp")
    if found:
        return found

    # 2. Prebuilt copy at util/lsp/bs-lsp-bin (created by `make`)
    here = Path(__file__).resolve().parent.parent  # util/lsp/
    candidate = here / "bs-lsp-bin"
    if candidate.is_file() and os.access(candidate, os.X_OK):
        return str(candidate)

    # 3. cabal dist-newstyle
    cabal_root = here / "bs-lsp"
    if cabal_root.is_dir():
        for p in cabal_root.rglob("bs-lsp"):
            if p.is_file() and os.access(p, os.X_OK) and "build/bs-lsp/bs-lsp" in str(p):
                return str(p)

    return None


def find_workspace_root(file_path: str) -> str:
    """Walk up from file_path looking for a repo/workspace root indicator."""
    p = Path(file_path).resolve().parent
    for ancestor in [p, *p.parents]:
        if (ancestor / ".git").exists():
            return str(ancestor)
        if (ancestor / "BUILD").exists() or (ancestor / "WORKSPACE").exists():
            return str(ancestor)
        if list(ancestor.glob("*.cabal")):
            return str(ancestor)
    return str(p)


# ── CLI ───────────────────────────────────────────────────────────────────────

def main() -> int:
    ap = argparse.ArgumentParser(
        description="Automated LSP integration tester for bs-lsp.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=(
            "Exit codes:\n"
            "  0  No crashes detected\n"
            "  1  One or more crashes detected\n"
            "  2  Tool error\n\n"
            "Examples:\n"
            "  # Test TV_Info.bsv, follow defs 2 levels deep:\n"
            "  python3 lsp_tester.py src_Core/ISA/TV_Info.bsv\n\n"
            "  # Reproduce a specific known crash:\n"
            "  python3 lsp_tester.py TV_Info.bsv --position 352:14\n\n"
            "  # Shallow test (no cross-file following) with JSON output:\n"
            "  python3 lsp_tester.py TV_Info.bsv --depth 0 --json results.json\n"
        ),
    )
    ap.add_argument("file", help="Seed BSV/BS file to test")
    ap.add_argument(
        "--lsp", default=None, metavar="PATH",
        help="Path to bs-lsp binary (default: auto-detect)",
    )
    ap.add_argument(
        "--workspace", default=None, metavar="DIR",
        help="Workspace root for LSP (default: nearest .git ancestor of FILE)",
    )
    ap.add_argument(
        "--depth", type=int, default=2, metavar="N",
        help="Levels of cross-file definition following (default: 2)",
    )
    ap.add_argument(
        "--positions", type=int, default=50, metavar="N",
        help="Max identifiers to sample from the seed file (default: 50)",
    )
    ap.add_argument(
        "--follow-positions", type=int, default=20, metavar="N",
        help="Max identifiers to sample per followed file (default: 20)",
    )
    ap.add_argument(
        "--timeout", type=float, default=10.0, metavar="SECS",
        help="Per-request timeout in seconds (default: 10.0)",
    )
    ap.add_argument(
        "--position", default=None, metavar="LINE:COL",
        help="Test only this 1-indexed position (useful to reproduce a specific crash)",
    )
    ap.add_argument(
        "--bluespec-src", default=None, metavar="DIR",
        help="Set BLUESPEC_SRC env var for the LSP server",
    )
    ap.add_argument(
        "--bluespecdir", default=None, metavar="DIR",
        help="Set BLUESPECDIR env var for the LSP server",
    )
    ap.add_argument(
        "--json", default=None, metavar="FILE",
        help="Write machine-readable JSON results to FILE",
    )
    ap.add_argument(
        "--verbose", "-v", action="store_true",
        help="Show all test results (default: show only crashes/timeouts)",
    )
    args = ap.parse_args()

    logging.basicConfig(
        level=logging.DEBUG if args.verbose else logging.INFO,
        format="%(message)s",
        stream=sys.stderr,
    )

    # Validate input file
    seed = str(Path(args.file).resolve())
    if not Path(seed).exists():
        print(f"Error: file not found: {args.file}", file=sys.stderr)
        return EXIT_TOOL_ERROR

    # Locate binary
    binary = args.lsp or find_lsp_binary()
    if not binary or not Path(binary).exists():
        print(
            "Error: bs-lsp binary not found.\n"
            "Build it with:  cd util/lsp && make\n"
            "or pass:        --lsp /path/to/bs-lsp",
            file=sys.stderr,
        )
        return EXIT_TOOL_ERROR
    if not os.access(binary, os.X_OK):
        print(f"Error: {binary} is not executable", file=sys.stderr)
        return EXIT_TOOL_ERROR

    # Workspace root
    workspace = args.workspace or find_workspace_root(seed)

    # Build environment for server
    env = os.environ.copy()
    if args.bluespec_src:
        env["BLUESPEC_SRC"] = args.bluespec_src
    if args.bluespecdir:
        env["BLUESPECDIR"] = args.bluespecdir

    # Parse --position
    specific_pos: Optional[tuple[int, int]] = None
    if args.position:
        try:
            parts = args.position.split(":")
            specific_pos = (int(parts[0]) - 1, int(parts[1]) - 1)  # to 0-indexed
        except (ValueError, IndexError):
            print(f"Error: --position must be LINE:COL (1-indexed), got: {args.position}",
                  file=sys.stderr)
            return EXIT_TOOL_ERROR

    # Banner
    log.info("bs-lsp    : %s", binary)
    log.info("workspace : %s", workspace)
    log.info("seed file : %s", relpath(seed))
    log.info("depth     : %d", args.depth)
    if args.bluespec_src:
        log.info("BLUESPEC_SRC : %s", args.bluespec_src)
    if args.bluespecdir:
        log.info("BLUESPECDIR  : %s", args.bluespecdir)
    log.info("")

    tester = Tester(
        binary=binary,
        workspace=workspace,
        env=env,
        max_depth=args.depth,
        positions_seed=args.positions,
        positions_follow=args.follow_positions,
        timeout=args.timeout,
    )

    tester.run(seed, specific_position=specific_pos)

    rc = print_report(tester.results, tester._restarts, json_path=args.json)
    return rc


if __name__ == "__main__":
    sys.exit(main())
