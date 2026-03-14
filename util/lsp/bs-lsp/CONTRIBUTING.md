# bs-lsp — Contributor Guide

`bs-lsp` is the Language Server Protocol implementation for Bluespec. It
communicates with editors (VS Code, Emacs, Vim/Neovim, etc.) over stdio using
the LSP JSON-RPC protocol, providing hover info, go-to-definition, completions,
and diagnostics for `.bs` and `.bsv` files.

---

## Repository Layout

```
bs-lsp/
├── bs-lsp.cabal
├── cabal.project            ← references ../bs-parser
├── app/Main.hs              ← binary entry point (runs on stdio)
└── src/Language/Bluespec/LSP/
    ├── Server.hs            ← initialisation, library discovery, workspace scan
    ├── State.hs             ← ServerState, DocumentState types
    ├── Handlers.hs          ← LSP request/notification dispatch
    ├── SymbolTable.hs       ← symbol extraction, library discovery
    ├── Definition.hs        ← go-to-definition
    ├── Hover.hs             ← hover info
    ├── Diagnostics.hs       ← parse errors → LSP diagnostics
    ├── Symbols.hs           ← document symbols (outline)
    └── Completion.hs        ← completions (scope, dot, import, keyword)
```

---

## Building and Testing

```bash
cd /work/bsc/util/lsp/bs-lsp
~/.ghcup/bin/cabal build
~/.ghcup/bin/cabal test bs-lsp-test
~/.ghcup/bin/cabal run bs-lsp   # runs on stdio; attach your editor
```

---

## Architecture

### State Model

`ServerState` (in `State.hs`) is the single source of truth. It holds:
- `ssDocuments :: Map Uri DocumentState` — all open files
- `ssModuleIndex :: ModuleIndex` — cross-file module index
- `ssPreludeSymbols :: SymbolTable` — standard library symbols
- `ssWorkspaceRoots :: [FilePath]`

All state access goes through a `TVar ServerState`. Handlers modify it
atomically. Background indexing writes to it from a separate thread.

### Parse → Document Pipeline

```
textDocument/didOpen | didChange
  → parseAuto (bs-parser)             -- produces Package AST
  → buildTypeEnv (TypeEnv.hs)         -- local bindings, typedef expansion
  → extractSymbols (SymbolTable.hs)   -- module-level symbol table
  → publishDiagnostics (Diagnostics)  -- parse errors as LSP diagnostics
```

Parse failures publish diagnostics but never crash the server. The symbol
table for a file is cleared on parse error (so stale data doesn't mislead).

### LSP Coordinate Conversion

The LSP protocol uses **0-indexed** line/column. The `bs-parser` uses
**1-indexed** positions. The conversion happens in `Definition.hs` and
`Hover.hs`. Never pass raw LSP positions to parser-produced `SrcPos` values.

### Symbol Resolution Order

1. Local document symbols
2. Qualified name lookup (module prefix → import)
3. Unqualified import scan
4. Prelude fallback

### Library Discovery

At startup, `SymbolTable.hs` looks for standard library sources in order:
1. `BLUESPEC_SRC` environment variable
2. `BLUESPECDIR` environment variable → `$BLUESPECDIR/Libraries/`
3. Bazel query (if in a Bazel workspace)
4. `getExecutablePath` → `../lib/lsp-libs/` (relative to binary)

---

## Adding a New LSP Feature

1. Add a handler in `Handlers.hs` (register it in the `handlers` list).
2. Implement the logic in a new or existing module under `LSP/`.
3. If you need new AST information, check `SymbolTable.hs` and `TypeEnv.hs`
   before reaching into the parser's `Package` type directly.
4. Add a test in `test/` using the HSpec + lsp-test framework.

---

## Key Invariants

- **False negatives over false positives**: a missed diagnostic/completion is
  better than a spurious one. Users will lose trust if the LSP cries wolf.
- **Never crash on bad input**: every handler should be wrapped in
  `catch`/`try`. An editor file is always mid-edit; expect the unexpected.
- **No blocking on main thread**: library indexing happens in a background
  thread. The main thread must remain responsive to LSP messages.

---

## VS Code Extension

The extension lives at `/work/bsc/util/lsp/vscode-bluespec/`. To add BSV
support, add `".bsv"` to the `languages[0].extensions` array in `package.json`.

To test the extension locally:
```bash
cd /work/bsc/util/lsp/vscode-bluespec
npm install
vsce package   # produces bluespec-*.vsix
# Install via VS Code: Extensions → ⋯ → Install from VSIX
```
