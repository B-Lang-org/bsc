#!/usr/bin/env python3
"""
Reproduce and verify the fix for the Prelude.bs hang in bs-lsp.

The bug: when VS Code navigates to Prelude.bs via go-to-definition, it sends
textDocument/didOpen with the full file content.  The server processes this
synchronously in the notification handler, blocking the message loop for the
duration of buildSymbolTable + buildTypeEnv + makeTypeMismatchDiagnostics on
the 4389-line Prelude.bs.  Any pending hover/definition requests during that
window get no response, so VS Code shows the server as "stuck".

The fix: make parseAndUpdateDocument run in a background thread so the
notification handler returns immediately.

Usage:
    python3 TestPreludeHang.py <path-to-bs-lsp> <path-to-Prelude.bs>

Exit codes:
    0  server responded to hover within 2 s of Prelude.bs didOpen  (PASS)
    1  server did not respond within 10 s                           (FAIL / still hung)
"""

import json
import subprocess
import sys
import time


# ---------------------------------------------------------------------------
# Minimal LSP client helpers
# ---------------------------------------------------------------------------

def send(proc, msg):
    body = json.dumps(msg, separators=(",", ":"))
    data = f"Content-Length: {len(body.encode())}\r\n\r\n{body}".encode()
    proc.stdin.write(data)
    proc.stdin.flush()


def recv(proc):
    hdr = b""
    while b"\r\n\r\n" not in hdr:
        ch = proc.stdout.read(1)
        if not ch:
            return None
        hdr += ch
    n = 0
    for line in hdr.split(b"\r\n"):
        if line.lower().startswith(b"content-length:"):
            n = int(line.split(b":", 1)[1].strip())
    if n == 0:
        return None
    return json.loads(proc.stdout.read(n))


# ---------------------------------------------------------------------------
# Main test
# ---------------------------------------------------------------------------

def main():
    if len(sys.argv) < 3:
        print(f"Usage: {sys.argv[0]} <bs-lsp-binary> <Prelude.bs>")
        sys.exit(2)

    bs_lsp_bin = sys.argv[1]
    prelude_path = sys.argv[2]

    with open(prelude_path) as fh:
        prelude_text = fh.read()

    print(f"Prelude.bs: {len(prelude_text):,} chars, {prelude_text.count(chr(10)):,} lines")

    proc = subprocess.Popen(
        [bs_lsp_bin],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )

    t0 = time.monotonic()

    # ---- initialize --------------------------------------------------------
    send(proc, {
        "jsonrpc": "2.0", "id": 1, "method": "initialize",
        "params": {
            "processId": 0,
            "capabilities": {},
            "rootUri": "file:///tmp",
        },
    })
    while True:
        msg = recv(proc)
        if msg and msg.get("id") == 1:
            break  # initialize response

    send(proc, {"jsonrpc": "2.0", "method": "initialized", "params": {}})

    # ---- open a small placeholder file so the server has a document --------
    # (hover will be sent for this URI; the result doesn't matter — we only
    #  care whether the server responds at all while Prelude.bs is being processed)
    small_uri = "file:///tmp/Dummy.bs"
    send(proc, {
        "jsonrpc": "2.0", "method": "textDocument/didOpen",
        "params": {
            "textDocument": {
                "uri": small_uri,
                "languageId": "bluespec",
                "version": 1,
                "text": "package Dummy where\n",
            },
        },
    })
    # Drain any notifications from the small-file open
    deadline = time.monotonic() + 2.0
    while time.monotonic() < deadline:
        # Non-blocking peek: give the server 2 s to settle
        import select
        ready, _, _ = select.select([proc.stdout], [], [], 0.1)
        if not ready:
            break
        recv(proc)  # discard

    # ---- open Prelude.bs ---------------------------------------------------
    t_open = time.monotonic()
    print(f"\n[{t_open - t0:.2f}s] Sending textDocument/didOpen for Prelude.bs ...")
    send(proc, {
        "jsonrpc": "2.0", "method": "textDocument/didOpen",
        "params": {
            "textDocument": {
                "uri": f"file://{prelude_path}",
                "languageId": "bluespec",
                "version": 1,
                "text": prelude_text,
            },
        },
    })

    # ---- immediately send a hover for the small file -----------------------
    # If the server is blocking on the didOpen handler it cannot service this.
    time.sleep(0.05)
    hover_id = 42
    print(f"[{time.monotonic() - t0:.2f}s] Sending textDocument/hover for Dummy.bs ...")
    send(proc, {
        "jsonrpc": "2.0", "id": hover_id, "method": "textDocument/hover",
        "params": {
            "textDocument": {"uri": small_uri},
            "position": {"line": 0, "character": 0},
        },
    })

    # ---- collect responses -------------------------------------------------
    HOVER_TIMEOUT = 10.0   # seconds to wait for hover response
    deadline = time.monotonic() + HOVER_TIMEOUT
    hover_at = None

    while time.monotonic() < deadline:
        import select
        ready, _, _ = select.select([proc.stdout], [], [], 0.5)
        if not ready:
            continue
        msg = recv(proc)
        if msg is None:
            break
        elapsed = time.monotonic() - t_open
        label = msg.get("method", f"response id={msg.get('id', '?')}")
        print(f"  [{elapsed:.2f}s] {label}")
        if msg.get("id") == hover_id:
            hover_at = elapsed
            break

    proc.terminate()

    # ---- verdict -----------------------------------------------------------
    PASS_THRESHOLD = 2.0  # seconds

    print()
    if hover_at is None:
        print(f"FAIL — hover never responded within {HOVER_TIMEOUT:.0f}s (server hung)")
        sys.exit(1)
    elif hover_at <= PASS_THRESHOLD:
        print(f"PASS — hover responded in {hover_at:.2f}s (server is non-blocking)")
        sys.exit(0)
    else:
        print(
            f"FAIL — hover took {hover_at:.2f}s (expected ≤ {PASS_THRESHOLD}s; "
            f"server is blocking on Prelude.bs processing)"
        )
        sys.exit(1)


if __name__ == "__main__":
    main()
