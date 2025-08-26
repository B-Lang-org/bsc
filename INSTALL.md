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
 - The standard Haskell compiler [GHC]. The recommended version is the
   latest 9.6 point release, but the Bluespec compiler should work
   with any release from 7.10.3 through 9.12.  We recommend installing
   GHC via the popular installer [GHCup].
 - A few additional Haskell libraries: `regex-compat`, `syb`,
   `old-time`, and `split`.
 - `pkg-config` is strongly recommended to query installed
   libraries. The build will fall back to default values if necessary,
   but this should be avoided if possible.
 - Standard unix shell and development tools, notably GNU Make.

The following dependencies are optional, though recommended:
 - To build the Yices SMT solver: a C/C++ toolchain, `autoconf` and
   the `gperf` perfect hashing library.
 - To build the STP SMT solver: a C/C++ toolchain, Perl, and the
   `flex` and `bison` parser generator tools.
 - To build the Bluespec Tcl shell (`bluetcl`): Tcl development
   libraries. Version 8 may be required, as we have not yet tested
   with version 9.
 - To run smoke tests: the [Icarus Verilog] simulator.
 - To run the full test suite: the Icarus Verilog simulator, Perl,
   csh, and SystemC libraries. See the [testsuite
   README](testsuite/README.md) for details.
 - To build PDF documentation: a LaTeX installation, with extras and
   additional fonts.
 - To format release notes for publication, the [Asciidoctor] tool.

[GHC]: https://www.haskell.org/ghc/
[GHCUp]: https://www.haskell.org/ghcup/
[Icarus Verilog]: https://steveicarus.github.io/iverilog/
[Asciidoctor]: https://asciidoctor.org

### Debian and Ubuntu systems

The following commands install all required and optional dependencies:

```bash
sudo apt-get install \
   build-essential \
   tcl-dev \
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
cabal update
cabal v1-install regex-compat syb old-time split
```

Those final four commands install the recommended GHC compiler version
and libraries. If you would prefer to install GHC via the system's
package manager, which may install an older version, you can
substitute the following command:

```bash
sudo apt-get install \
   ghc \
   libghc-regex-compat-dev \
   libghc-syb-dev \
   libghc-old-time-dev \
   libghc-split-dev
```

However, if you use the package manager and want to profile the
Bluespec compiler (unlikely for most users), you will also need to the
profiling-enabled versions of the Haskell libraries:

```bash
sudo apt-get install \
   ghc-prof \
   libghc-regex-compat-prof \
   libghc-syb-prof \
   libghc-old-time-prof \
   libghc-split-prof
```

### Fedora systems

The following commands install all required and optional dependencies:

```bash
sudo dnf install \
   @development-tools \
   @c-development \
   iverilog \
   dejagnu \
   tcl-devel \
   gperf \
   latex \
   texlive-scheme-basic \
   texlive-moreverb \
   texlive-dingbat \
   texlive-subfigure

curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | sh
ghcup install ghc 9.6.7
cabal update
cabal v1-install regex-compat syb old-time split
```

Note that `tcl8-devel` may be needed in place of `tcl-devel`, until we have
tested with Tcl v9.

Those final four commands install the recommended GHC compiler version
and libraries. If you would prefer to install GHC via the system's
package manager, which may install an older version, you can
substitute the following command:

```bash
sudo dnf install \
   ghc \
   ghc-regex-compat-devel \
   ghc-syb-devel \
   ghc-old-time-devel \
   ghc-split-devel
```

However, if you use the package manager and want to profile the
Bluespec compiler (unlikely for most users), you will also need to the
profiling-enabled versions of the Haskell libraries:

```bash
sudo dnf install \
   ghc-prof \
   ghc-regex-compat-prof \
   ghc-syb-prof \
   ghc-old-time-prof \
   ghc-split-prof
```

### GHC Haskell compiler

As shown in the above summaries, we recommend installing GHC via the
popular installer [GHCup], which is available for Linux, FreeBSD,
macOS, and WSL2 on Windows.  This allows easily installing the
recommended version of GHC. The package manager for your OS may
provide a package for GHC, however it may be for an older version of
GHC.  This is fine, as the BSC source code has been written with
extensive preprocessor macros to support every minor release of GHC
since 7.10, through 9.12. Any releases in that range should be fine;
however, newer versions may be more efficient.
GHC releases older than 7.10.3 are not supported.

BSC releases are tested and built with the recommended stable version
of GHC, currently 9.6.7.  The source is also tested with a range of
newer GHC versions (currently 9.8, 9.10, and 9.12) any of which are
also fine.

### Haskell libraries via Cabal

Building BSC requires some additional Haskell libraries beyond the standard
GHC libraries.  We recommend using the `cabal` command to install
those libraries, as shown in the above summaries.
As with GHC, we recommend installing `cabal` via `ghcup`.

If you have installed GHC through the package manager of your OS,
then you may need to install libraries through the package manager as
well (as shown in the above summaries) or you may need to install `cabal`
through the package manager.

The BSC build currently assumes that libraries have been installed
globally with GHC.  This is why we have shown the `cabal` command
using the legacy `v1-install` subcommand, which install globally:

```bash
cabal update
cabal v1-install regex-compat syb old-time split
```

Cabal's newer `v2-install` has the advantage of not installing the
libraries into the GHC installation.  This is useful if the GHC
installation is globally installed and you want to build BSC without
disturbing the global setup; or if GHC is installed via a package
manager and you don't want to mix cabal-installed files with package
manager-installed files.  Using `v2-install` is possible, but requires
passing an additional flag to GHC, which can be done by defining `GHC`
in the environment when calling `make` in the later steps.  For
example (cabal 3.x only):

```bash
cabal v2-install --package-env=default syb old-time split
make GHC="ghc -package-env default"
```

To build a version of BSC that supports profiling, be aware that
profiling versions of the libraries need to be installed.

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
make PREFIX=/opt/tools/bsc/bsc-${BSC_VERSION}
```

However, note that the `clean` target will delete the `PREFIX` directory!

An unoptimized, debug, or profiling build can be done using one of:

```bash
make BSC_BUILD=NOOPT
make BSC_BUILD=DEBUG
make BSC_BUILD=PROF
```

You can provide the `-j` flag to `make` to specify the number of targets
to execute in parallel, however this does not control the parallelism of
the core haskell build.  To specify the number of modules that GHC may
compile in parallel, define `GHCJOBS` in the environment to that number:

```bash
make GHCJOBS=4
```

### Optionally avoiding the compile of STP or Yices

The BSC tools need an SMT solver. By default, the build process
compiles both the Yices and STP solvers, and allows the end user to
select which one to use at runtime, with Yices being the default.

Most users will never need to switch solvers, or even be aware of the
option. Thus, the build process offers the option of not compiling one
of the two solvers.

Currently, the BSC executable expects to dynamically link with
object files for Yices and STP found in the directory `inst/lib/SAT/`.
BSC calls a function in the library to query its version; if the version
does not match what BSC expects, BSC will not let users select that solvers.
Thus, the current way to omit a solver is to replace the object file
with a stub that returns a null version.  In the future, we may replace
this with static linking and the processing for removing a solver 
would then simply omit the code for that solver.

To skip building the STP solver, assign a non-empty value to
`STP_STUB`:

```bash
make STP_STUB=1
```

Similarly, use `YICES_STUB` to skip building the Yices solver:

```bash
make YICES_STUB=1
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

For two, you may wish to adjust files in the `src/comp/` directory, to
give a particular version name to installations built from the
snapshot.  The build in that directory uses Git to automatically
generate the version information for the compiler and place it in the
file `BuildVersion.hs`.  The script that generates this,
`update-build-version.sh`, can only query Git for version info when
called from inside a Git repository.  The script will still work if
`git archive` is used to export the snapshot, because we have
specified (in `.gitattributes`) that patterns in the file should be
substituted with their values (the commit hash and tag, if any) during
export.  Therefore, no change in this directory is required.  However,
if you want to hard-code a different version name, you can pre-generate
the `BuildVersion.hs` file and adjust the `Makefile` to not rebuild
it, by changing the assignment of `NOUPDATEBUILDVERSION` to `1`.

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
