<div class="title-block" style="text-align: center;" align="center">

# Bluespec Compiler

[![Version]](https://github.com/B-Lang-org/bsc/releases/tag/2026.01)
[![License]](./COPYING)
[![Build Status]](https://github.com/B-Lang-org/bsc/actions/workflows/ci.yml?query=branch%3Amain+event%3Apush)

[License]:        https://img.shields.io/badge/license-BSD%203-blueviolet.svg
[Version]:        https://img.shields.io/badge/release-2026.01-red.svg?logo=v
[Build Status]:   https://github.com/B-Lang-org/bsc/actions/workflows/ci.yml/badge.svg?branch=main&event=push

**[Community] &bull; [Download] &bull; [Documentation] &bull; [Build] &bull; [Test] &bull; [Develop] &bull; [bbt]**

[Community]: #community
[Download]: #download
[Documentation]: #documentation
[Build]: ./INSTALL.md
[TEST]: ./testsuite/README.md
[Develop]: ./DEVELOP.md
[bbt]: #build-tool-bbt

---

</div>

Compiler, simulator, and tools for the **Bluespec Hardware Description
Language**. Bluespec is a single language for digital electronic hardware designs that comes in
two syntactic flavors, which are interchangeable:

  - Bluespec **SystemVerilog** (BSV)
  - Bluespec **Haskell** (BH, or "Bluespec Classic")

Bluespec is a *high-level* hardware description language. It has a variety of
advanced features including a powerful type system that can prevent errors
prior to synthesis time, and its most distinguishing feature, **Guarded Atomic
Actions**, allow you to define hardware components in a modular manner based on
their invariants, and let the compiler pick a scheduler.

The toolchain was under development by [Bluespec Inc] for almost 20 years, and
has been proven repeatedly in production designs like [Flute], [Piccolo], and
[Shakti].

The Bluespec compiler `bsc` emits standard Verilog for maximum compatibility
with any synthesis toolchain and comes with an included simulator ("bluesim"),
standard library, and TCL scripting support ("bluetcl").

The repository is still evolving. We welcome your feedback, issue reports,
and pull requests.

A separate repository, [bsc-contrib],
exists for sharing libraries and utilities that don't (or don't yet) belong in
the core tools.

A graphical environment for using BSC is available in a separate [bdw]
repository. BDW (the BSC Development Workstation) provides a number of
tools, including the ability to view simulation waveforms as
source-level values.

[Bluespec Inc]: https://bluespec.com
[Flute]: https://github.com/bluespec/Flute
[Piccolo]: https://github.com/bluespec/Piccolo
[Shakti]: https://shakti.org.in

[bsc-contrib]: https://github.com/B-Lang-org/bsc-contrib
[bdw]: https://github.com/B-Lang-org/bdw

---

## Community

To receive announcements about BSC and related projects, subscribe to
[b-lang-announce@groups.io](https://groups.io/g/b-lang-announce).

For questions and discussion about BSC source, subscribe to the
developers' mailing list [bsc-dev@groups.io](https://groups.io/g/bsc-dev).

For any questions or discussion about Bluespec HDLs, using BSC, or
related projects, subscribe to [b-lang-discuss@groups.io](https://groups.io/g/b-lang-discuss).

IRC users might try joining the `#bluespec` channel on [Libera.Chat](https://libera.chat/).

There's also a [bluespec](https://stackoverflow.com/questions/tagged/bluespec)
tag on StackOverflow.

And we've enabled the [Discussions](https://github.com/B-Lang-org/bsc/discussions)
tab in this GitHub repo.
This is a new feature to support discussion within the project itself.
Feel free to give it a try and see if it can be useful to our community.

---

## Download

For the following systems, the Bluespec toolchain is available
as a package that can be installed with the standard package manager:

* ArchLinux AUR: [`bluespec-git`](https://aur.archlinux.org/packages/bluespec-git/) ([among others](https://aur.archlinux.org/packages/?K=bluespec))
* Gentoo GURU and LiGurOS: [`sci-electronics/bluespec`](https://gitweb.gentoo.org/repo/proj/guru.git/tree/sci-electronics/bluespec)
* Nix/NixOS: [`bluespec`](https://search.nixos.org/packages?channel=20.09&from=0&size=50&sort=relevance&query=bluespec)

You can also use the [Repology search engine](https://repology.org/project/bluespec/versions)
to check for Bluespec packages for your system.

If a package exists for your system, we recommend installing that.
Otherwise, a tar-archive may be available for download from our
[Releases](https://github.com/B-Lang-org/bsc/releases) page.
Install instructions can be found inside the tar-file.

If a pre-built tar-file does not exist for your system,
you will need to [compile BSC from source](INSTALL.md).

---

## Documentation

More details on using BSC, Bluesim, and Bluetcl can be found in the
[_BSC User
Guide_](https://github.com/B-Lang-org/bsc/releases/latest/download/bsc_user_guide.pdf).

The standard libraries that come with BSC are documented in the [_BSC
Libraries Reference
Guide_](https://github.com/B-Lang-org/bsc/releases/latest/download/bsc_libraries_ref_guide.pdf).

For the specification of the Bluespec language, see the [_BSV Language
Reference
Guide_](https://github.com/B-Lang-org/bsc/releases/latest/download/BSV_lang_ref_guide.pdf)
and the [_BH (Bluespec Haskell/Classic) Language Reference
Guide_](https://github.com/B-Lang-org/bsc/releases/latest/download/BH_lang_ref_guide.pdf).

The sources for these documents are found in the `doc`
directory of this repo.  Pre-built PDF files can also be downloaded
from the [Releases](https://github.com/B-Lang-org/bsc/releases) page.

Training and tutorials can be found in the [BSVLang
repository](https://github.com/BSVLang/Main).

New users may also find this
[Intro Guide and Quick Reference](https://github.com/kcamenzind/BluespecIntroGuide)
useful.

---

## Build Tool (bbt)

`bbt` is a project-aware build tool for Bluespec — roughly "cargo for
Bluespec".  It wraps `bsc` with a project manifest (`bsc.toml`) so you
don't have to manage `-p` paths, `-bdir`/`-vdir` directories, or long
flag lists by hand.  `bbt` is built and installed alongside `bsc` by
`make install-src`.

### Quick start

```bash
# Create a new BSV project (use 'bs' for Classic/BH syntax)
bbt new bsv my_project
cd my_project

# Compile and run in Bluesim
bbt sim

# Synthesise to Verilog
bbt build

# Check for package-name conflicts across source files
bbt check

# Generate HTML documentation from --@ doc-comments
bbt doc                  # writes to docs/
bbt doc --out site/docs  # custom output directory
```

### `bsc.toml` format

`bbt new` generates a ready-to-use `bsc.toml`.  A typical file looks
like this:

```toml
[package]
name    = "my_project"
version = "0.1.0"

[build]
top_file   = "src/Top.bsv"    # file containing the top-level module
top_module = "mkTop"           # module to elaborate / simulate
src        = "src"             # source directory (scanned recursively)

[[target.default]]
build_dir   = "build/bdir"     # .bo / .ba intermediate files
sim_dir     = "build/sim"      # Bluesim output
verilog_dir = "build/verilog"  # synthesised Verilog output
```

Additional knobs available in `bsc.toml`:

| Section / key | Purpose |
|---|---|
| `[flags]` | Toggle common `bsc` flags (`aggressive_conditions`, `keep_fires`, `check_assert`, …) |
| `[flags] extra` | Arbitrary extra flags passed verbatim to `bsc` |
| `[defines]` | Preprocessor defines (`KEY = "value"`) |
| `[[conflict]]` | Resolve duplicate package names across source trees |
| `[profile.NAME]` | Named build variants (e.g. `debug` vs `release`) |
| `[[target.NAME]]` | Multiple output targets (e.g. separate sim and synth targets) |

### Command reference

| Command | What it does |
|---|---|
| `bbt new (bs\|bsv) NAME` | Scaffold a new project in `./NAME/` |
| `bbt build` | Compile to Verilog (default target) |
| `bbt build -t NAME` | Compile a named `[[target.NAME]]` |
| `bbt build --dry-run` | Print the `bsc` invocation without running it |
| `bbt sim` | Compile for Bluesim and execute the simulation |
| `bbt sim -- +bscvcd` | Pass extra arguments to the simulation binary |
| `bbt check` | Detect package-name conflicts; exit non-zero if any |
| `bbt doc` | Generate HTML docs from `--@` doc-comments |
| `bbt clean` | Remove build artefacts |
| `bbt show sources` | List every source file that will be passed to `bsc` |
| `bbt show flags` | Print the full `bsc` command that `build` would run |
| `bbt show conflicts` | List conflicting package names (if any) |
| `bbt lsp-info` | Emit JSON project info consumed by `bs-lsp` |

Use `--profile NAME` (or `-p NAME`) with `build`, `sim`, `check`, and
`show` to select a named profile from `bsc.toml`.

### Doc-comments

`bbt doc` extracts documentation from `--@`-prefixed comment lines and
generates a Haddock-style HTML site.  The comment syntax supports a
LaTeX subset including `\emph{}`, `\te{}`, `\begin{verbatim}`, lists,
and inline math:

```bsv
//@ Returns a FIFO with capacity \te{n}.
//@ Raises a dynamic error if \te{n} is zero.
module mkMyFifo#(Integer n)(FIFO#(a));
```

The generated site is written to `docs/` by default and is fully
self-contained (no external CDN dependencies at view time).

---

## Editor Support

The `util/` directory contains editor integrations for several editors
(`emacs/`, `vim/`, `jedit/`).  For editors that support the
[Language Server Protocol](https://microsoft.github.io/language-server-protocol/)
(VS Code, Neovim, Emacs with `lsp-mode`, etc.), BSC ships a dedicated
language server: **`bs-lsp`**.

`bs-lsp` is built and installed alongside `bsc` by `make install-src`.
It provides:

- **Hover** — type signatures and kind information on demand
- **Go-to-definition** — jump to the definition of any symbol, including
  standard library packages like `Vector`, `FIFO`, `StmtFSM`, etc.
- **Diagnostics** — parse errors highlighted inline as you type

### VS Code

A VS Code extension is included at `util/lsp/vscode-bluespec/`.
After building BSC, install it with:

```bash
# Requires Node.js / npm
make install-vscode-ext
```

Then add `inst/bin` to your `PATH` (or set `bluespec.serverPath` in VS Code
settings to the full path of `bs-lsp`), open a `.bs` file, and the language
server will start automatically.

### Other LSP clients

Point your client at the `bs-lsp` binary (found in `inst/bin/` after
`make install-src`) and use `stdio` transport.  Set the `BLUESPECDIR`
environment variable to the `inst/` directory so that `bs-lsp` can
locate the standard library:

```bash
export BLUESPECDIR=/path/to/bsc/inst
```

---

## License

The Bluespec toolchain is provided by [Bluespec Inc] and
available under the BSD-3-Clause license.
The source code also includes several other components under
various license agreements (all of it open/copyleft software).
See [`COPYING`](COPYING) for copyright and license details.
