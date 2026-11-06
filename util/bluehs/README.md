# Haskell scripts against the bsc library

The programs `bsc.cabal` builds as executables can also be run as scripts,
by `runghc` against the **compiled** bsc library rather than compiled to
binaries of their own. `ghci` works the same way, giving an interactive
session with the whole compiler importable.

There is no second copy of any program here. `runghc` executes a file's
`main` whatever its module is called, so `src/comp/app/dumpbo.hs` --- the
same file the `dumpbo` executable is built from, module `Main_dumpbo` ---
is also the script. The launcher in this directory resolves a tool name to
that file and runs it.

## Setup

    make install-src

`make install-src` builds the library along with `bsc`, at the repository
root, and writes the `.ghc.environment.*` file that names it. The launcher
uses that library, and the installed tree under `inst` (the default
`PREFIX`) for the solvers and `BLUESPECDIR`. Make refreshes
`src/comp/BuildVersion.hs` before building (doc/cabal.md section 4).

**Re-run `make install-src` after pulling or switching commits**, not a
bare `cabal build`, which can leave the version stale. This is a
correctness requirement, not hygiene: `.bo`/`.ba` files embed the build
version string (git hash), and the library rejects `.ba` files whose stamp
differs from its own (`EBinFileVerMismatch`). The library and the `bsc` that
produced your files must share a `BuildVersion.hs`.

## Running scripts

Through the launcher, from anywhere; it sets `GHC_ENVIRONMENT` and the
solver path, and `BLUESPECDIR` when it is unset:

    util/bluehs/bin/dumpbo foo.bo
    util/bluehs/bin/showrules -o out.vcd mkTop dump.vcd

Inside the repository, `runghc` alone also finds the library, through the
`.ghc.environment.*` file; `cabal exec` leaves it out, as make built it
with options (`GHCRTSFLAGS`) that `cabal exec` is not given. `runghc` does
not set `BLUESPECDIR` (which `showrules` and `vcdcheck` read) or the solver
path, so give it `BLUESPECDIR=$PWD/inst/lib` and, on Linux,
`LD_LIBRARY_PATH=$PWD/inst/lib/SAT` to avoid a warning per solver library
(on macOS the rpath resolves the solvers and the warning is silenced with
`--ghc-arg=-Wno-missed-extra-shared-lib`, as the launcher does):

    runghc src/comp/app/dumpba.hs foo.ba

`bin/` carries a symlink per tool, named after it, pointing at the
`bluehs` launcher, which dispatches on the name it was invoked as. The
launcher also takes a path to any `.hs` file, so a script of your own runs
the same way, as does a program of `bsc.cabal` that has no symlink here:

    util/bluehs/bluehs my-analysis.hs design.ba
    util/bluehs/bluehs src/comp/app/bsc.hs -verilog Foo.bsv

Modules beside the script are found; other directories of a script split
across several modules are named with `-i`, before the script, as `runghc`
would take them. The working directory is searched only when it holds the
script, so a file there named like a compiler module (`Util.hs`,
`Error.hs`) cannot otherwise shadow the library's:

    util/bluehs/bluehs -imy-lib my-tool/Main.hs design.ba

Standard output is block-buffered unless it is a terminal, as in the
compiled tools. Startup cost is ~0.3-0.5s: the library is compiled, and
only the entry file is interpreted.

## Interactive use

    ghci        # anywhere inside the repo (but see the .ghci caveat below)
    ghci> :m + GenBin ISyntax PPrint Error
    ghci> import qualified Data.ByteString as BS
    ghci> errh <- initErrorHandle
    ghci> bs <- BS.readFile "inst/lib/Libraries/Arbiter.bo"
    ghci> (bi, bo, ipkg, hash) <- readBinFile errh "Arbiter.bo" bs
    ghci> putStr (ppReadable bi)

Every module the library exposes is importable --- parsers, type checker,
`ISyntax`/`ASyntax`, `.bo`/`.ba` (de)serialization, VCD handling,
scheduling. (`cabal repl bsc` also works but interprets the library from
source, which is much slower to load.)

## Caveats and invariants

* **Do not start `ghci` with cwd `src/comp`.** The `src/comp/.ghci` there
  (for the interpret-from-source workflow) is merged into the session and
  fights the package environment. Use the repository root, or
  `ghci -ignore-dot-ghci`.
* **The solver libraries are loaded, not linked in.** `bsc.cabal` names
  `libstp` and `libyices` in `extra-libraries`, so every script and every
  `ghci` session opens them at load, and the library's shared object records
  them as dependencies. They come from the installed tree, `inst/lib/SAT`:
  the launcher names it in `LD_LIBRARY_PATH` for GHC's loader, and the
  shared object carries the rpath that resolves them (`cabal.project`), the
  build tree's `lib/SAT` beside it pointing at the installed copies. The
  distribution's registration names its own `SAT` directory; its `ghci`
  needs only the package environment and `BLUESPECDIR`:

      GHC_ENVIRONMENT=inst/bluehs/hs/bsc.env BLUESPECDIR=inst/lib \
          inst/bluehs/hs/ghc/bin/ghci
* **On Linux, a compiled program needs a Tcl link option.** The library
  compiles in the Tcl binding but leaves Tcl's symbols to the `bluetcl`
  executable, which links Tcl, so a program linked against its shared
  library (`-dynamic`, the only kind the distribution ships) needs
  `-optl-Wl,--allow-shlib-undefined`.
* **`BLUESPECDIR` must name a real `inst/lib`** for the tools that read it
  (`showrules` and `vcdcheck` use it for `%` expansion and default `.ba`
  search paths). The launcher defaults it to `<repo>/inst/lib`, which is
  where `make install-src` puts it with the default `PREFIX`; after
  `make install-src PREFIX=<dir>`, set `BLUESPECDIR=<dir>/lib` yourself.

## Distribution

`make install-bluehs` runs `make install-src` and then installs a
self-contained copy of all this at `inst/bluehs`: a pruned GHC runtime, a
package store holding the compiled bsc library and its dependencies, the
SAT solver libraries, the tool entry scripts (every program of `bsc.cabal`
but `bluetcl`), and this launcher as `bin/bluehs`. It runs scripts with
**no Haskell toolchain installed**, and the tree can be moved with the rest
of `inst`:

    inst/bluehs/bin/bluehs dumpbo foo.bo
    inst/bluehs/bin/bluehs -imy-lib my-tool/Main.hs design.ba

It needs from the host only the C and C++ runtimes, libgmp and libtinfo
(ncurses), and, for scripts that use CPP, the C compiler the shipped GHC
was configured with, by name (`gcc` for the Linux bindist); other scripts
run with no C compiler reachable.
`util/bluehs/mk-dist.sh` does the work; it needs `ghc` and `cabal` on `PATH`
(the GHC it ships, or the one `GHC` names), `python3`, `cpio`, and
`patchelf` on Linux, and takes the make build's `GHC`, `GHCJOBS`,
`GHCRTSFLAGS` and `BSC_BUILD` settings and the checkout's
`cabal.project.local`. It builds the project a second time from another
directory, so the checkout's own build and environment file are untouched,
and resolves dependencies against the project's `index-state` into the
cabal store rather than one under the checkout, whose path the files a
dependency builds would record. It ships the bsc library and its
dependencies and no build tool, strips the solver libraries, and fails if
any file still names the checkout, or the work directory or the GHC
installation outside the header lists that interface files keep for
recompilation. Before installing, it runs a copy of the tree from another
directory under an empty environment with a probe script that imports the
compiler's modules, and checks that the library's build version matches
`inst/bin/bsc`'s and that the probe is the only module interpreted, so the
compiler's modules come from the compiled library; a tree that fails
leaves the installed one in place. The program list is the one the build
hooks write (`SetupHooks.hs`), so a later program needs no change here.

Build it in the same tree as the `bsc` beside it: the library rejects `.ba`
files whose build version stamp differs (see Caveats).

Everything redistributed is covered in `inst/bluehs/LICENSES/`: `COPYING`
lists the components, with BSC's own terms (`COPYING.bsc`), the texts the
release ships for code adapted into the compiler and for the bundled solver
libraries, GHC's license and libffi's, and a generated `LICENSE.ghc_pkgs`
naming every shipped Haskell package that declares a license, with its
copyright (via `src/comp/make-ghc-pkg-info.sh`; GHC's own undeclared
packages fall under `LICENSE.ghc`).

## Not converted

* `bsc` itself: works as a script mechanically, but the ~1.5s/invocation
  interpretation cost of the 2300-line driver is wrong for a tool invoked
  once per compilation unit.
* `bluetcl`: structurally not a script: its Haskell `main` hands control to
  Tcl through a C shim (`bluetcl_shim.c`) compiled into the executable, which
  an interpreted run cannot supply.
