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

    util/bluehs/setup.sh

The cabal hooks build the vendored solver libraries and regenerate
`BuildVersion.hs`, so nothing has to be prepared by hand. The first build
compiles the library's 239 modules; later ones are incremental.

**Re-run `setup.sh` whenever you rebuild bsc at a new commit.** This is a
correctness requirement, not hygiene: `.bo`/`.ba` files embed the build
version string (git hash), and the library rejects `.ba` files whose stamp
differs from its own (`EBinFileVerMismatch`). The library and the `bsc` that
produced your files must share a `BuildVersion.hs`.

## Running scripts

Three equivalent ways, most convenient first:

    # from anywhere --- the launcher sets GHC_ENVIRONMENT and BLUESPECDIR:
    util/bluehs/bin/dumpbo foo.bo
    util/bluehs/bin/showrules -o out.vcd mkTop dump.vcd

    # from inside the repo --- GHC finds .ghc.environment.* by upward search:
    runghc src/comp/app/dumpba.hs foo.ba

    # explicit project context:
    cabal exec -v0 -- runghc src/comp/app/bsc2bsv.hs Foo.bs

`bin/` carries a symlink per tool, named after it, pointing at the
`bluehs` launcher, which dispatches on the name it was invoked as. The
launcher also takes a path to any `.hs` file, so a script of your own runs
the same way, as does a program in `src/comp/app` that has no symlink here:

    util/bluehs/bluehs my-analysis.hs design.ba
    util/bluehs/bluehs src/comp/app/bsc.hs -verilog Foo.bsv

Startup cost is ~0.3-0.5s: the library is compiled, and only the entry
file is interpreted.

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
* **The solver libraries are loaded, not linked in.** The cabal hooks name
  the vendored `libstp` and `libyices` in the library's `extra-libraries`, so
  every script and every `ghci` session opens them at load. The hooks also
  name one rpath covering the vendored directories, which is what resolves
  them: each solver records itself `@rpath`-relative on Mach-O, and by its
  soname on ELF.
* **`BLUESPECDIR` must name a real `inst/lib`** for the tools that read it
  (`showrules` and `vcdcheck` use it for `%` expansion and default `.ba`
  search paths). The launcher defaults it to `<repo>/inst/lib`, which is
  where `make install-src` puts it.

## Distribution

`util/bluehs/mk-dist.sh` builds `bsc-bluehs-<os>-<arch>-<version>.tar.gz`: a
self-contained, relocatable tree (pruned GHC runtime + relocatable package
store + SAT solver libraries + the tool entry scripts + a `bin/bluehs`
launcher) so
tarball users can run Haskell scripts against the bsc library with **no
Haskell toolchain installed**. Host requirements: glibc, libgmp, libtcl8.6,
and a C compiler (GHC probes it when loading libraries; CPP scripts
preprocess with it).

This artifact is a *companion* to the main bsc tarball and must be built
from the same commit (the packaged library rejects `.ba` files whose build
version stamp differs — see Caveats). Ship both from one release action;
they are versioned in lockstep, like bluetcl.

Everything redistributed in the tarball is covered in its `LICENSES/`
directory: `LICENSE.ghc` (compiler/runtime), a generated
`LICENSE.ghc_pkgs` enumerating every shipped Haskell package with license
and copyright (via `src/comp/make-ghc-pkg-info.sh` over the exact shipped
package closure), and the STP/Yices texts for the bundled solver
libraries.

The scripts in this tarball provide what `make install-extra` builds as
compiled binaries; once bluehs ships as a standard release artifact,
`install-extra` is a candidate for retirement.

## Not converted

* `bsc` itself: works as a script mechanically, but the ~1.5s/invocation
  interpretation cost of the 2300-line driver is wrong for a tool invoked
  once per compilation unit. The right eventual shape is moving `hmain` into
  a library module (`Driver`), making `bsc` a 3-line compiled `Main` — after
  which custom driver *scripts* are trivial for those who want them.
* `bluetcl`: structurally not a script — it embeds Haskell in a C `main` via
  foreign exports and links libtcl/libhtcl.
