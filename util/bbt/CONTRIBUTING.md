# bbt — Contributor Guide

`bbt` is the Bluespec Build Tool — "cargo for Bluespec". It wraps `bsc` with
a project-aware `bsc.toml` manifest, replacing hand-written Makefiles for new
projects and providing the LSP with reliable project structure information.

---

## Repository Layout

```
bbt/
├── bbt.cabal
├── cabal.project            ← references ../lsp/bs-parser and ../docgen
├── app/Main.hs              ← CLI entry point (optparse-applicative)
└── src/Language/Bluespec/BBT/
    ├── Config.hs            ← bsc.toml parsing (toml-parser)
    ├── Discover.hs          ← source file scanning, conflict detection
    ├── Build.hs             ← bsc invocation, flag assembly
    ├── Project.hs           ← findBscToml: search upward from cwd
    ├── LspInfo.hs           ← JSON output for LSP (lsp-info subcommand)
    ├── Doc.hs               ← bbt doc: thin wrapper over bs-docgen
    ├── New.hs               ← bbt new: project scaffolding
    └── Sim.hs               ← bbt sim: Bluesim compilation + execution
```

---

## Building

```bash
cd /work/bsc/util/bbt
~/.ghcup/bin/cabal build
~/.ghcup/bin/cabal run bbt -- --help
```

---

## Subcommands

| Command | Module | Description |
|---|---|---|
| `bbt build` | `Build.hs` | Invoke `bsc` with flags from `bsc.toml` |
| `bbt check` | `Discover.hs` | Detect package-name conflicts; syntax check |
| `bbt clean` | `Main.hs` | Remove build artefacts (stub; not yet implemented) |
| `bbt doc` | `Doc.hs` | Generate HTML docs via `bs-docgen` |
| `bbt lsp-info` | `LspInfo.hs` | Emit JSON project info for the LSP |
| `bbt new bs\|bsv NAME` | `New.hs` | Scaffold a new project directory |
| `bbt show` | `Main.hs` | Show sources, conflicts, or bsc flags |
| `bbt sim` | `Sim.hs` | Compile for Bluesim and run the simulation |

---

## `bsc.toml` Manifest Format

```toml
[package]
name    = "MyProject"
version = "0.1.0"

[build]
top_file   = "src/Top.bsv"
top_module = "mkTop"
src        = "src"             # or src = ["src", "lib"]

[[target.default]]
build_dir   = "build/bdir"
sim_dir     = "build/sim"
verilog_dir = "build/verilog"

# Optional: multiple targets
[[target.verilog-only]]
verilog_dir = "build/verilog"
build_dir   = "build/bdir"
```

The `[build]` section sets global parameters. Named `[[target.NAME]]` sections
define build variants (Bluesim, Verilog, etc.). `bbt build` picks the first
target by default; `bbt build --target verilog-only` picks a named one.

---

## Adding a New Subcommand

1. Create `src/Language/Bluespec/BBT/MyCmd.hs` with a `MyOpts` type and
   a `runMyCmd :: Config -> MyOpts -> IO ()` function.
2. Add `Language.Bluespec.BBT.MyCmd` to `exposed-modules` in `bbt.cabal`.
3. Add the parser and `CmdMyCmd !MyOpts` variant in `app/Main.hs`.
4. Wire `CmdMyCmd opts -> withBbtConfig gopts (\cfg -> runMyCmd cfg opts)`
   in the `run` function.

---

## `bbt new` — Project Scaffolding

`bbt new bs NAME` or `bbt new bsv NAME` creates:

```
NAME/
├── bsc.toml         ← minimal manifest
├── src/
│   └── Top.bs       ← hello world + counter-to-5 example (or Top.bsv)
└── .gitignore
```

The generated project is immediately runnable with `bbt sim`.

## `bbt sim` — Bluesim Simulation

`bbt sim` compiles with `bsc -sim -e MODULE` and then executes the resulting
simulation binary. Extra arguments after `--` are forwarded to the binary:

```bash
bbt sim                 # compile + run
bbt sim -- +bscvcd      # pass +bscvcd to the sim binary
bbt sim --target foo    # use the [target.foo] section
```

---

## Key Design Decisions

- **All rendering logic lives in `bs-docgen`**: `bbt doc` is a thin wrapper
  that calls `runDocGen`. No HTML rendering in `bbt`.
- **`Config` is strict** (`StrictData` extension): fields are forced on parse,
  so TOML errors surface at startup, not mid-build.
- **Conflict detection before building**: `Discover.hs` checks for duplicate
  package names across all source directories before invoking `bsc`.
