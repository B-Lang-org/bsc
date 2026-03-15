# lsp-tester

A black-box integration test harness for `bs-lsp`, the Bluespec Language Server.

## What it does

`lsp-tester` starts `bs-lsp` as a subprocess and systematically exercises:

- **`textDocument/hover`** — type inference; does the server return type information for this symbol?
- **`textDocument/definition`** — go-to-definition; does it resolve to the right location?

It scans a seed BSV/BS file for identifier tokens, tests each one, then **follows cross-file definitions** (into stdlib, Prelude, imported modules, etc.) up to a configurable depth.  The primary goal is to detect **server crashes** — the main failure mode when navigating into standard-library files.

Soft failures (null responses — "no hover for this token") are logged but not counted as errors.  Only crashes (server process dies) and timeouts (no response within the timeout) are flagged.

## Requirements

- Python 3.9+, stdlib only — no `pip install` required
- A built `bs-lsp` binary (see below)

## Building bs-lsp

```bash
cd /path/to/bsc/util/lsp
make              # builds bs-lsp and copies it to util/lsp/bs-lsp-bin
```

Or build manually:

```bash
cd util/lsp/bs-lsp
~/.ghcup/bin/cabal build exe:bs-lsp
# binary at: dist-newstyle/.../bs-lsp
```

## Usage

```
python3 lsp_tester.py [OPTIONS] FILE.bsv
```

### Common invocations

```bash
# Test a file; follow definitions 2 levels deep (the default)
python3 lsp_tester.py src_Core/ISA/TV_Info.bsv

# Reproduce the known Prelude.bs crash: test a specific position
python3 lsp_tester.py src_Core/ISA/TV_Info.bsv --position 352:14

# Tell the server where to find the stdlib
python3 lsp_tester.py TV_Info.bsv --bluespec-src /work/bsc

# Shallow scan — only the seed file, no cross-file following
python3 lsp_tester.py TV_Info.bsv --depth 0

# Deep scan with verbose output and JSON report
python3 lsp_tester.py TV_Info.bsv --depth 3 --verbose --json report.json

# Specify the binary and workspace explicitly
python3 lsp_tester.py TV_Info.bsv \
  --lsp /work/bsc/util/lsp/bs-lsp-bin \
  --workspace /work/Flute
```

### All options

| Flag | Default | Description |
|------|---------|-------------|
| `FILE` | *(required)* | Seed BSV/BS file to start from |
| `--lsp PATH` | auto-detect | Path to `bs-lsp` binary |
| `--workspace DIR` | nearest `.git` ancestor | Workspace root for LSP |
| `--depth N` | `2` | Levels of cross-file definition following |
| `--positions N` | `50` | Max identifiers sampled from the seed file |
| `--follow-positions N` | `20` | Max identifiers sampled per followed file |
| `--timeout SECS` | `10.0` | Per-request timeout in seconds |
| `--position LINE:COL` | *(none)* | Test only this 1-indexed position |
| `--bluespec-src DIR` | *(from env)* | Sets `BLUESPEC_SRC` for the server |
| `--bluespecdir DIR` | *(from env)* | Sets `BLUESPECDIR` for the server |
| `--json FILE` | *(none)* | Write machine-readable results to JSON file |
| `--verbose` / `-v` | false | Print all results (default: crashes/timeouts only) |

### Binary auto-detection order

1. `bs-lsp` on `PATH`
2. `util/lsp/bs-lsp-bin` (built by `make`)
3. Cabal `dist-newstyle/…/bs-lsp` (built by `cabal build`)

### Library auto-detection

The LSP server finds the Bluespec standard library via (in order):

1. `BLUESPEC_LIB_DIR` env var
2. `BLUESPEC_SRC` env var → `$BLUESPEC_SRC/src/Libraries`
3. `BLUESPECDIR` env var → `$BLUESPECDIR/Libraries`
4. Bazel query (if running inside a Bazel workspace)
5. Path relative to the `bs-lsp` binary

If none of these work the server will still run but hover/definition for stdlib symbols will return null rather than crashing.  Use `--bluespec-src /work/bsc` to point at a source checkout.

## Output

Progress lines go to **stderr**; the final report goes to **stdout**.

### Progress symbols

| Symbol | Meaning |
|--------|---------|
| `✓` | Hover or definition returned a result |
| `·` | Null response — server alive but no result for this token (normal) |
| `💥` | **Crash** — server process died |
| `⏱` | **Timeout** — no response within `--timeout` seconds |
| `!` | Error response (JSON-RPC `error` field present) |

Example progress line:
```
  zeroExtend@352:14         hover=· def=→  [cross-file] → lib-srcs/Libraries/Base1/Prelude.bs:1756
```

### Final report

```
════════════════════════════════════════════════════════════════════════
  lsp-tester report
════════════════════════════════════════════════════════════════════════
  Positions tested  : 87
  Server restarts   : 1
  Hover OK          : 42
  Definition OK     : 31
  Cross-file defs   : 12
  Timeouts          : 0
  CRASHES           : 1

  ────────────────────────────────────────────────────────────────────
  CRASHES
  ────────────────────────────────────────────────────────────────────
  lib-srcs/Libraries/Base1/Prelude.bs:1756:1  (zeroExtend)  [hover]
      stderr▸  bs-lsp: Prelude.bs: <<loop>>
      stderr▸  bs-lsp: CallStack (from HasCallStack): error, called at …

  ────────────────────────────────────────────────────────────────────
  CROSS-FILE DEFINITIONS
  ────────────────────────────────────────────────────────────────────
  src_Core/ISA/TV_Info.bsv:352:14  zeroExtend  →  Prelude.bs:1756
  …
════════════════════════════════════════════════════════════════════════
```

## Exit codes

| Code | Meaning |
|------|---------|
| `0` | No crashes detected |
| `1` | One or more crashes detected |
| `2` | Tool error (binary not found, file unreadable, etc.) |

## How it works

1. **Start `bs-lsp`** as a subprocess communicating over stdio JSON-RPC (standard LSP protocol).
2. Send `initialize` / `initialized` to set up the workspace.
3. Send `textDocument/didOpen` for the seed file.
4. **Scan for identifiers**: strip comments and string literals, deduplicate by name, sample evenly up to `--positions`.
5. For each identifier:
   - Send `textDocument/hover` → record result
   - Send `textDocument/definition` → record result + target location
   - If the server dies at any point, record a crash with the last `N` lines of stderr, restart, and continue.
6. **Depth following**: any definition that resolves to a *different* file is queued for depth+1 testing.  The target location itself (the exact destination line) is always included in the next level's position list, so the hotspot is always exercised.
7. Repeat until the queue is empty or `--depth` is reached.

### Why cross-file navigation crashes

When a user navigates to a definition in `Prelude.bs` (or another stdlib file), the editor sends `textDocument/didOpen` for that file followed by hover/definition requests *within* it.  `bs-lsp` must then parse and index a file it may not have seen before — often triggering edge-cases in the parser or symbol-table code.  `lsp-tester` reproduces this exactly: after obtaining a cross-file definition location it opens that file and tests positions within it.

### Explosion prevention

| Mechanism | Default |
|-----------|---------|
| `--depth` cap | 2 — files at depth > 2 are never enqueued |
| `--follow-positions` cap | 20 — at depth ≥ 1, only 20 positions per file |
| Global visited set | `(file, line, col)` triples are never tested twice |
| File dedup | Each unique target file is only followed once per depth level |

## Known limitations

- Operator symbols (e.g. `+`, `<=`) are not tested — only alphanumeric identifiers.
- Hover text parsing is best-effort; if the server returns an unusual `contents` shape it may be logged as null.
- On very large workspaces the background indexing the server does after `initialize` may not be complete when the first hover request arrives, causing false nulls.  Use `--timeout` to give the server more time if needed.
