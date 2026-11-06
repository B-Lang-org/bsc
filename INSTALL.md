# Compiling BSC from source

Source code for the Bluespec toolchain can currently be built on Linux
and macOS. It may compile for other flavors of Unix, but likely will need
additional if/else blocks in source code or Makefiles.

The core of BSC is written in Haskell, with some libraries in C/C++.

---

## Overview

The following sections describe the requirements and commands for building
BSC.  Running the build commands will result in the creation of a directory
(named `inst` by default) that contains an _installation_ of BSC.  This
directory can be moved to anywhere on your system, but it is best for the
files to remain in their relative positions within the directory.

We recommend renaming the `inst` directory to `bsc-${BSC_VERSION}` and placing
it in a subdirectory of `/opt/`, `${HOME}/`, `/usr/share/`, or similar
location.  For example:

```bash
BSC_VERSION=$(echo 'puts [lindex [Bluetcl::version] 0]' | inst/bin/bluetcl)
mkdir -p /opt/tools/bsc
mv inst /opt/tools/bsc/bsc-${BSC_VERSION}
cd /opt/tools/bsc
ln -s bsc-${BSC_VERSION} latest
```

The `inst` directory has a `bin` subdirectory, where the executables
for the tools are found.  To use the tools, just add that directory to
your `PATH`:

```bash
export PATH=/opt/tools/bsc/latest/bin:$PATH
```

These executables will make use of other files found within the `inst`
directory, locating them relatively from the `bin` directory.  That is
why the directory must be kept together.

If you are packaging BSC for an OS (for example, into a `.deb` or `.rpm`
file), your package can't simply move the `bin` files to `/usr/bin/`
and the `lib` files to `/usr/lib/` and so on.  We recommend placing the
`inst` directory at `/usr/share/bsc/bsc-${BSC_VERSION}` and then creating
symlinks in `/usr/bin/` that point to the executables in
`/usr/share/bsc/bsc-${BSC_VERSION}/bin/`.

---

## Requirements

To build a complete release of BSC, you will need:
 - The standard Haskell compiler [GHC]. The recommended version is
   9.6.7, which is the primary version built and tested by this
   project's continuous integration (CI); other versions, 9.4.7
   through 9.14, are also tested (see the [CI workflow] for the exact
   set).  Older versions are not supported.  We recommend installing
   GHC via the popular installer [GHCup].
 - The Haskell build tool [cabal-install], version 3.16, which fetches
   the Haskell libraries the build needs beyond GHC's own from Hackage.
   We recommend installing it via [GHCup] as well.
 - The GNU Multiple Precision Arithmetic Library (GMP). `libgmp` is
   used to implement integers in Haskell and may already be a
   dependency of installing GHC.
 - `pkg-config` is strongly recommended to query installed
   libraries. The build will fall back to default values if necessary,
   but this should be avoided if possible.
 - Standard unix shell and development tools, notably GNU Make.
 - Tcl development libraries (version 9.0, 8.6, or 8.5). The Cabal package
   builds `bluetcl` and the compiler's Tcl binding as part of every full build.

The following dependencies are optional, though recommended:
 - To build the Yices SMT solver: a C/C++ toolchain, `autoconf` and
   the `gperf` perfect hashing library.
 - To build the STP SMT solver: a C/C++ toolchain, Perl, and the
   `flex` and `bison` parser generator tools.
 - To run smoke tests: the [Icarus Verilog] simulator.
 - To run the full test suite: the Icarus Verilog simulator, Perl,
   csh, and SystemC libraries. See the [testsuite
   README](testsuite/README.md) for details.
 - To build PDF documentation: a LaTeX installation, with extras and
   additional fonts.
 - To format release notes for publication, the [Asciidoctor] tool.

[CI workflow]: .github/workflows/ci.yml
[GHC]: https://www.haskell.org/ghc/
[GHCUp]: https://www.haskell.org/ghcup/
[cabal-install]: https://www.haskell.org/cabal/
[Icarus Verilog]: https://steveicarus.github.io/iverilog/
[Asciidoctor]: https://asciidoctor.org

### Debian and Ubuntu systems

The following commands install all required and optional dependencies:

```bash
sudo apt-get install \
   build-essential \
   tcl-dev \
   libgmp-dev \
   pkg-config \
   autoconf \
   gperf \
   flex \
   bison \
   iverilog \
   texlive-latex-base \
   texlive-latex-recommended \
   texlive-latex-extra \
   texlive-font-utils \
   texlive-fonts-extra

curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | sh
ghcup install ghc 9.6.7
ghcup install cabal 3.16.1.0 --set
cabal update
```

Those final four commands install the recommended GHC compiler version
and the cabal build tool, and fetch the package index the build reads.
If you would prefer to install GHC via the system's
package manager, which may install an older version, you can
substitute the following command.  Any `ghc` from 9.4.7 through 9.14 builds the
compiler, Ubuntu 24.04's included (see the GHC section below); an older
`ghc`, such as Ubuntu 22.04's 8.8.4 (check with `ghc --version`), is not
supported.

```bash
sudo apt-get install ghc
```

If you use the system's package manager and want to profile the
Bluespec compiler (unlikely for most users), you will also need the
profiling-enabled versions of GHC's own libraries:

```bash
sudo apt-get install ghc-prof
```

The distribution's `cabal-install` is usually too old for this build, so
install 3.16 with [GHCup] as in the summary above
(`ghcup install cabal 3.16.1.0 --set`).

### Fedora systems

The following commands install all required and optional dependencies:

```bash
sudo dnf install \
   @development-tools \
   @c-development \
   iverilog \
   dejagnu \
   tcl-devel \
   gmp-devel \
   gperf \
   latex \
   texlive-boxedminipage \
   texlive-dingbat \
   texlive-fancybox \
   texlive-moreverb \
   texlive-scheme-basic \
   texlive-subfigure

curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | sh
ghcup install ghc 9.6.7
ghcup install cabal 3.16.1.0 --set
cabal update
```

Those final four commands install the recommended GHC compiler version
and the cabal build tool, and fetch the package index the build reads.
If you would prefer to install GHC via the system's
package manager, which may install an older version, you can
substitute the following command.  Any `ghc` from 9.4.7 through 9.14 builds the
compiler (see the GHC section below); a `ghc` older than 9.4.7 (check
with `ghc --version`) is not supported.

```bash
sudo dnf install ghc
```

If you use the system's package manager and want to profile the
Bluespec compiler (unlikely for most users), you will also need the
profiling-enabled versions of GHC's own libraries:

```bash
sudo dnf install ghc-prof
```

The distribution's `cabal-install` is usually too old for this build, so
install 3.16 with [GHCup] as in the summary above
(`ghcup install cabal 3.16.1.0 --set`).

### MacOS systems

BSC builds on MacOS running on newer Apple (arm64) chips and older
Intel (x86_64) chips.  We test on MacOS 13 (x86_64), MacOS 14 (arm64),
and MacOS 15 (arm64).  To build on MacOS, you need the Command Line
Tools from Apple's [Xcode] app.  With Xcode installed, the following
command will install the Command Line Tools:

```bash
xcode-select --install
```

[XCode]: https://apps.apple.com/us/app/xcode/id497799835

We use the [Homebrew] package manager to install dependencies.  After
the [Xcode] Command Line Tools are installed, [Homebrew] can be
installed with the following command from their website:

```bash
/bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"
```

[Homebrew]: https://brew.sh

After [Homebrew] is installed, the following commands install all
required and optional dependencies:

```bash
brew update
brew install \
   autoconf \
   gmp \
   gperf \
   icarus-verilog \
   pkg-config \
   deja-gnu \
   systemc \
   asciidoctor \
   texlive

curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | sh
ghcup install ghc 9.6.7
ghcup install cabal 3.16.1.0 --set
cabal update
```

Those final four commands install the recommended GHC compiler version
and the cabal build tool, and fetch the package index the build reads.

### GHC Haskell compiler

As shown in the above summaries, we recommend installing GHC via the
popular installer [GHCup], which is available for Linux, FreeBSD,
macOS, and WSL2 on Windows.  This allows easily installing the
recommended version of GHC. The package manager for your OS may
provide a package for GHC, however it may be for an older version of
GHC.  This is fine, as the BSC source code builds with every release
of GHC from 9.4.7, the version Ubuntu 24.04 packages, through 9.14; newer
versions in that range may be more efficient.  GHC releases older than 9.4.7
are not supported, and a release newer than 9.14 needs the upper bounds in
`bsc.cabal` raised (or `allow-newer: bsc:*` in `cabal.project.local`).

BSC releases are tested and built with the recommended stable version
of GHC, currently 9.6.7.  The source is also tested with a range of
other GHC versions (currently 9.4.7, and 9.8 through 9.14) any of which
are also fine.

### Haskell libraries via Cabal

`make install-src` uses Cabal to build the Haskell compiler package; see
[the Cabal build guide](doc/cabal.md). Cabal fetches dependencies from Hackage
into its store under your home directory. No libraries need to be installed by
hand, and the build does not modify the GHC installation.

Install `cabal-install` 3.16.1.0 with `ghcup install cabal 3.16.1.0 --set`
(older releases reject `bsc.cabal`'s `cabal-version: 3.16`; 3.18 builds it
too, but warns `Semaphore version mismatch` and compiles the library serially
on GHC 9.12-9.14). Run
`cabal update` to fetch the Hackage index; if your local index predates the
`index-state` in `cabal.project`, run `cabal update` again.

To build BSC with profiling enabled (`make install-src BSC_BUILD=PROF`), profiling
libraries for GHC's bundled packages must be installed (`ghc-prof` when using
an OS-packaged GHC); Cabal builds profiling versions of Hackage dependencies
automatically.

### SMT solvers

The repository for the [Yices SMT Solver] is cloned as a submodule of
this repository. Building the BSC tools will recurse into this
directory and build the Yices library for linking into BSC and
Bluetcl.

[Yices SMT Solver]: https://github.com/SRI-CSL/yices2

Building the BSC tools will also recurse into a directory for the STP
SMT solver. This is currently an old snapshot of the STP source code,
including the code for various libraries that it uses. In the future,
this may be replaced with a submodule instantiation of the repository
for the [STP SMT solver]. When that happens, additional requirements
from that repository will be added.

[STP SMT solver]: https://github.com/stp/stp

Both the Yices and STP solvers are optional to build, although
recommended. To skip these builds, see "Optionally avoiding the
compile of STP or Yices" below.

## Clone the repository

Clone this repository by running:

```bash
git clone --recursive https://github.com/B-Lang-org/bsc
```

That will clone this repository and all of the submodules that it depends on.
If you have cloned the repository without the `--recursive` flag, you can setup
the submodules later with a separate command:

```bash
git clone https://github.com/B-Lang-org/bsc
git submodule update --init --recursive
```

## Build the BSC toolchain

At the root of the repository:

```bash
make install-src
```

This will create a directory called `inst` containing an installation of the
compiler toolchain. This `inst` directory can later be moved to another
location; the tools do not hard-code the install location.

If you wish, you can install into another location by assigning the variable
`PREFIX` in the environment:

```bash
make install-src PREFIX=/opt/tools/bsc/bsc-${BSC_VERSION}
```

The `full_clean` target deletes the `PREFIX` directory; `clean` removes
intermediate build files (`build`, `dist-newstyle`, and `.ghc.environment.*`)
and keeps the installation.

An unoptimized, debug, or profiling build can be done using one of:

```bash
make install-src BSC_BUILD=NOOPT
make install-src BSC_BUILD=DEBUG
make install-src BSC_BUILD=PROF
```

See [Project settings and variants](doc/cabal.md#5-project-settings-and-variants)
for the settings each selects and local overrides, including the built
programs' default RTS options. Select GHC through Make's `GHC` variable:

```bash
make install-src GHC=ghc-9.14.1
```

You can provide the `-j` flag to `make` to specify the number of targets
to execute in parallel, however this does not control the parallelism of
the cabal build of the compiler.  To set that, define `GHCJOBS` in the
environment:

```bash
make install-src GHCJOBS=4
```

The [Cabal build guide](doc/cabal.md#5-project-settings-and-variants) explains
how this limit applies to each supported GHC version.

### Optionally avoiding the compile of STP or Yices

The BSC tools need an SMT solver. By default, the build process
compiles both the Yices and STP solvers, and allows the end user to
select which one to use at runtime, with Yices being the default.

Most users will never need to switch solvers, or even be aware of the
option. Thus, the build process offers the option of not compiling one
of the two solvers.

BSC dynamically links both solver libraries. The options below replace one
with a stub that BSC recognizes as unavailable. At startup, BSC calls
`checkVersion` for the selected solver; the stub fails this check, so that
backend cannot be selected. See
[Solvers](doc/cabal.md#solvers) for library lookup and compatibility.

To skip building the STP solver, assign a non-empty value to
`STP_STUB`:

```bash
make install-src STP_STUB=1
```

Similarly, use `YICES_STUB` to skip building the Yices solver:

```bash
make install-src YICES_STUB=1
```

The BSC tools do need at least one SMT solver, so only one of these
options should be used.

## Test the BSC toolchain

The following command will run a smoke test to ensure the compiler and
simulator work properly:

```bash
make check-smoke
```

For more extensive testing, see the [testsuite README]
in the `testsuite` subdirectory.

### Choosing a Verilog simulator

By default, the smoke test uses [Icarus Verilog] to test the Verilog code generation.
The Makefile in `examples/smoke_test` shows how you can point the default
`check-smoke` target at other Verilog simulators such as [Verilator],
VCS and VCSI (Synopys), NC-Verilog & NCsim (Cadence), ModelSim (Mentor), and CVC.

[Verilator]: https://www.veripool.org/wiki/verilator

## Build documentation

To build and install the PDF documentation, you can add the following:

```bash
make install-doc
```

This will install into the same `inst` or `PREFIX` directory.
The installed documents include the [BSC User Guide]
and the [BSC Libraries Reference Guide].

[BSC User Guide]: https://github.com/B-Lang-org/bsc/releases/latest/download/bsc_user_guide.pdf
[BSC Libraries Reference Guide]: https://github.com/B-Lang-org/bsc/releases/latest/download/bsc_libraries_ref_guide.pdf

The `bluehs` script runtime, which runs Haskell scripts against the compiled
compiler library on a machine with no Haskell toolchain, is installed beside
the compiler by

```
make install-bluehs
```

It needs `python3`, `cpio` and, on Linux, `patchelf`; see
`util/bluehs/README.md`.

## Building a release

The Makefile provides a single target, `release`, that will perform the above
steps (of building the tools and the docs) and will also install a few
additional files, creating a complete release in the `inst` directory:

```bash
make release
```

The additional files include a README, copyright and licensing info,
and release notes.  The release notes are written in
[AsciiDoc](https://asciidoc.org/) format that is published to HTML and
PDF format using the [Asciidoctor] tool, which is therefore a
requirement for building a release.

If you do not have Asciidoctor or would prefer not to install it (and all of
its dependencies), you can set `NOASCIIDOCTOR` in the environment:

```bash
make NOASCIIDOCTOR=1 release
```

This will install the raw AsciiDoc release notes, but will not install
the HTML and PDF versions.

## Exporting the source code

If you wish to make a snapshot of the source code available, outside
of Git, you can do so with `git archive`, but be aware of two points.

For one, you will need to also export the files from submodules,
because Git will not include them.

For two, the version information the compiler and the Bluesim kernel
carry is generated from Git by `src/comp/update-build-version.sh`, which
the build runs. The script queries Git in its own source tree when Git
metadata is available, regardless of the caller's directory. `git archive`
also works: `.gitattributes` marks the script for substitution of the commit
hash and tag, if any, during export. No manual change is required.

To freeze the recorded version or supply a custom release name, retain or
edit `src/comp/BuildVersion.hs` and build with
`make install-src NOUPDATEBUILDVERSION=1`. If the file is absent, the first
build generates it. The compiler and Bluesim use this same version; include
the file when distributing a source snapshot with a custom version.
Omit the option to resume generating version information from Git.
`make full_clean` deletes the file, so keep a copy outside the tree.

---

## Using the Bluespec compiler

The installation contains a `bin` directory. To run the BSC tools, you only
need to add the `bin` directory to your path (or provide that path on the
command line). The executables in that directory will expect to find other
files in sibling directories within that same parent installation directory. If
you just built the compiler, you can quickly test it like so:

```bash
export PATH=$(pwd)/inst/bin:$PATH
```

> **NOTE**: Earlier versions of BSC required that the environment variable
> `BLUESPECDIR` be set to point into the installation directory; this is no
> longer necessary, as the executables will figure out their location and
> determine the installation location on their own.

Run the following to see command-line options on the executable:

```bash
bsc -help
```

Additional flags of use to developers can be displayed with the
following command:

```bash
bsc -help-hidden
```

More details on using BSC, Bluesim, and Bluetcl can be found in the
[BSC User Guide] (built in this repository).
For language documentation and learning materials, see the
[Documentation section of the README](./README.md#documentation).

## Editors

Support for various editors for BH/BSV sources as well as language
server support for the haskell sources for the bluespec compiler can
be found in the [./util](./util) directory.
