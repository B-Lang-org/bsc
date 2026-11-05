# Deterministic BSC builds with Cabal

## 1. Determinism requirements

For the same commit, toolchain, dependencies, and build options, serial,
parallel, and relocated builds must produce identical binaries so that
compiler behavior does not depend on how it was built. An incremental build
after an edit and revert must produce the same bytes.

Validation of these requirements is incomplete. To achieve them, the build:

- Compiles the compiler library once and links every executable against it (section 2).
- Loads external package interfaces in a deterministic order via `Warmup` (section 4).
- Enables `-fobject-determinism` on GHC >= 9.12, and compiles each package
  serially on older GHCs (section 5).
- Links solvers by name with relative runtime paths (`rpath`), avoiding solver
  build paths in link settings (section 3).
- Strips symbols matching `ghc_*` from Linux executables to remove temporary
  GHC link-stub filenames after linking (section 4).
- Tracks the selected version so incremental builds reflect Git metadata or
  an explicitly frozen version (section 4).

## 2. Package layout

[`bsc.cabal`](../bsc.cabal) uses `build-type: Hooks`: one library containing
the compiler, vendored Parsec, and Tcl and solver bindings, plus eight
executables whose entry modules live under `src/comp/app`.

The library lists its modules in `exposed-modules`; `-Werror=missing-home-modules`
rejects any imported module missing from the list. The generated `Warmup` module is
listed in `autogen-modules`; `BuildVersion` is an ordinary module that the
build refreshes in `src/comp`.

Most of the file is Cabal's explicit inventory of modules, dependencies, and
components. Common stanzas share their settings; the module list and
dependency bounds need updating when those inputs change.

## 3. Building

After installing the [prerequisites](../INSTALL.md), build from the repository
root:

```bash
make install-src
```

This builds the vendored solvers, builds and installs `bsc` and `bluetcl` and
supporting libraries under `inst`. `make -C src/comp install-extra` builds and
installs the six utility executables, and `make -C src/comp bsc` builds a single
executable and symlinks it in `src/comp`. Pass the same `PREFIX`, `GHC`, and
`BSC_BUILD` flags across invocations.

### Solvers

The normal Make build installs the vendored `stp` and `yices` under
`inst/lib/SAT` and passes that directory through `LIBRARY_PATH`. The Cabal
package links both libraries by name, keeping the solver build directory out
of the package registration. At runtime, executables locate the solvers via a
relative `rpath` (`../lib/SAT` relative to `bin/`) or standard system paths.

`make install-solvers` builds and installs just the solvers. For
`Missing (or bad) C libraries: stp, yices`, build the solvers with the same
`PREFIX` as the compiler build and retry the compiler target. Avoid Cabal's
suggested `--extra-lib-dirs`, which records the directory in the package
registration.

BSC can use system solver shared libraries with compatible names and ABIs.
The standard Make build still builds and installs the vendored copies; it
has no option to select only system libraries. At least one real solver is
required; [INSTALL.md](../INSTALL.md#optionally-avoiding-the-compile-of-stp-or-yices)
describes replacing one backend with a stub.

## 4. Build hooks and generated files

[`SetupHooks.hs`](../SetupHooks.hs) configures Tcl, generates `Warmup`,
refreshes `BuildVersion`, arranges solver lookup in the build tree, and performs the
Linux symbol cleanup. Its comments describe the implementation.

`Warmup` works around observed GHC rewrite-rule nondeterminism caused by
external-interface load ordering.
It is separate from the object-code ordering addressed by
`-fobject-determinism`. Every root module in the library (one importing no
other library module) must `import Warmup ()`.
`src/comp/check-warmup-roots.sh` checks this invariant.

`src/comp/update-build-version.sh` maintains `src/comp/BuildVersion.hs` as
the version shared by the compiler and Bluesim. Make refreshes it before
invoking Cabal, and the hook runs the same script, so a `cabal build` run by
hand refreshes it too; both keep a custom or frozen file when
`NOUPDATEBUILDVERSION=1` is in the environment. The module is also listed in
`extra-source-files`, so a changed version rebuilds the package even when no
other source changed.
See [Exporting the source code](../INSTALL.md#exporting-the-source-code)
for Git archives and frozen or custom versions.

## 5. Project settings and variants

[`cabal.project`](../cabal.project) enables parallel module compilation on
GHC >= 9.12 with `-fobject-determinism` enabled for all packages.
`semaphore: True` shares a single job limit across
`cabal` and `ghc`. Older GHCs compile each package serially while still
building independent dependency packages in parallel.

`GHCJOBS` (default: processor count, capped at 16) sets `cabal build -j`. The
project also sets `optimization: 2` and writes `.ghc.environment.*` files for
`ghci` and `runghc` (`src/comp/.ghci`).

`index-state` pins the Hackage snapshot used to resolve dependencies.
See [INSTALL.md](../INSTALL.md#haskell-libraries-via-cabal)
for the required Cabal version and index setup.
Dependencies are built into Cabal's shared store (the directory
`cabal path --store-dir` reports) rather than a per-checkout store, both to
avoid rebuilding dependencies across checkouts
and because the shared library's `rpath` references the store path.

Each build variant imports `cabal.project`:

| Make option | Project file | Change |
| --- | --- | --- |
| `BSC_BUILD=NOOPT` | `cabal.project.noopt` | Disable optimization. |
| `BSC_BUILD=DEBUG` | `cabal.project.debug` | Add `-dcore-lint -debug` to `bsc`. |
| `BSC_BUILD=PROF` | `cabal.project.prof` | Enable profiling (`all-functions`) and `-with-rtsopts=-H256m -K256m -i1`. |

For example, `make install-src BSC_BUILD=PROF`. Put local overrides in
`cabal.project.local`, or `cabal.project.<variant>.local` for a variant.
To increase the built programs' default stack cap from
10 MiB to 32 MiB while preserving their other normal RTS defaults, put this
in `cabal.project.local`:

```cabal
package bsc
  ghc-options: "-with-rtsopts=-H256m -K32m -i1"
```

For a profiling build, use `cabal.project.prof.local` instead and choose the
stack cap appropriate for that build (the profiling default is 256 MiB).
Make selects GHC with `GHC=`. Its `GHCRTSFLAGS` variable controls GHC's own
runtime while compiling BSC; it does not set the built programs' RTS defaults.

`Setup.hs` is provided only because `cabal check` requires it for
`build-type: Hooks`.

## 6. Adding modules and executables

Add library modules under one of the library's `hs-source-dirs` and list them
in `exposed-modules` in `bsc.cabal`. If a new module imports no other library
modules, add `import Warmup ()`.

Add executable entry modules under `src/comp/app` with `module Main_<name>` and
declare the stanza in `bsc.cabal`:

```cabal
executable example
  import: common_exes
  ghc-options: -main-is Main_example
  main-is: example.hs
```

Add the name to the matching list in `src/comp/Makefile` (`UTILEXES` for a
utility) so that `make` builds and installs it.
