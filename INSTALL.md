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

We recommend renaming the `inst` directory to `bsc-<VERSION>` and placing
it in a subdirectory of `/opt/`, `${HOME}/`, `/usr/share/`, or similar
location.  For example:

    $ BSC_VERSION=$(echo 'puts [lindex [Bluetcl::version] 0]' | inst/bin/bluetcl)
    $ mkdir -p /opt/tools/bsc
    $ mv inst /opt/tools/bsc/bsc-${BSC_VERSION}
    $ cd /opt/tools/bsc
    $ ln -s bsc-${BSC_VERSION} latest

The `inst` directory has a `bin` subdirectory, where the executables
for the tools are found.  To use the tools, just add that directory to
your `PATH`:

    $ export PATH=/opt/tools/bsc/latest/bin:$PATH

These executables will make use of other files found within the `inst`
directory, locating them relatively from the `bin` directory.  That is
why the directory must be kept together.

If you are packaging BSC for an OS (for example, into a `.deb` or `.rpm`
file), your package can't simply move the `bin` files to `/usr/bin/`
and the `lib` files to `/usr/lib/` and so on.  We recommend placing the
`inst` directory at `/usr/share/bsc/bsc-<VERSION>` and then creating
symlinks in `/usr/bin/` that point to the executables in
`/usr/share/bsc/bsc-<VERSION>/bin/`.

---

## Install the Haskell compiler (GHC)

You will need the standard Haskell compiler `ghc` which is available for Linux,
macOS and Windows, along with some additional Haskell libraries. These are
available as standard packages in most Linux distributions. For example, on
Debian and Ubuntu systems, you can say:

    $ apt-get install ghc
    $ apt-get install \
        libghc-regex-compat-dev \
        libghc-syb-dev \
        libghc-old-time-dev \
        libghc-split-dev

The second command will install the Haskell libraries `regex-compat`, `syb`,
`old-time`, and `split`, as well as some libraries that they depend on.

If you wish to do profiling builds of the compiler itself, you will also need
to install versions of the Haskell libraries built using the profiling flags.
On Debian and Ubuntu, this can be done with:

    $ apt-get install \
        ghc-prof \
        libghc-regex-compat-prof \
        libghc-syb-prof \
        libghc-old-time-prof \
        libghc-split-prof

You can do the analogous package-install on other Linux distributions using
their native package mechanisms, and on macOS using Homebrew or Macports. Full details
can be found at <https://www.haskell.org/>, and in particular `ghcup` is a popular
installer for recent Haskell releases <https://www.haskell.org/ghcup/>.

On some systems, you may need to use the `cabal` command to install Haskell
libraries.  This tool is installed by `ghcup` but is also available as a package
for many distributions.
If you are using cabal 3.0 or later, you will need to use the legacy `v1-`
commands to install Haskell libraries.

For cabal v2.x:

    $ cabal update
    $ cabal install regex-compat syb old-time split

For cabal v3.x:

    $ cabal update
    $ cabal v1-install regex-compat syb old-time split

Cabal's newer `v2-install` has the advantage of not installing the
libraries into the GHC installation.  This is useful if the GHC
installation is globally installed and you want to build BSC without
disturbing the global setup; or if GHC is installed via a package
manager and you don't want to mix cabal-installed files with package
manager-installed files.  Using `v2-install` is possible, but requires
passing an additional flag to GHC, which can be done by defining `GHC`
in the environment when calling `make` in the later steps.
For example (cabal v3.x only):

    $ cabal v2-install --package-env=default syb old-time split
    $ make GHC="ghc -package-env default"

Bluespec compiler builds are tested with GHC 9.4.8.
GHC releases older than 7.10.3 are not supported.

The source code has been written with extensive preprocessor macros to
support every minor release of GHC since 7.10, through 9.8. Any releases
in that range should be fine.
The recommended version of GHC is 9.4 in its latest point release.

## Additional requirements

For building and using the Bluespec Tcl shell (`bluetcl`),
you will need the `tcl` library:

    $ apt-get install tcl-dev

Building BSC also requires standard Unix shell and Makefile utilities.
For example, in our testing on Ubuntu, we install the `build-essential` package
that pulls in the `make` package as a requirement.

    $ apt-get install build-essential

Some Makefiles will attempt to use `pkg-config` to query the installed libraries,
but will fall-back on default values if it is not available.  For best results
and to avoid spurious warnings, we recommend installing the `pkg-config`
package (or `pkgconfig` on some systems):

    $ apt-get install pkg-config

The repository for [the Yices SMT Solver](https://github.com/SRI-CSL/yices2) is
cloned as a submodule of this repository. Building the BSC tools will recurse
into this directory and build the Yices library for linking into BSC and
Bluetcl.
Building the Yices library is optional (see below), but recommended.
Yices currently requires `autoconf` and the `gperf` perfect hashing
library to compile:

    $ apt-get install \
        autoconf \
        gperf

Building the BSC tools will also recurse into a directory for the STP SMT
solver. This is currently an old snapshot of the STP source code, including the
code for various libraries that it uses. In the future, this may be replaced
with a submodule instantiation of the repository for [the STP SMT
solver](https://github.com/stp/stp). When that happens, additional requirements
from that repository will be added.
Building the STP library is optional (see below).
The current snapshot requires Perl, to
generate two source files. It also needs flex and bison:

    $ apt-get install flex bison

The `check-smoke` target runs a test using an external Verilog simulator, which is
[Icarus Verilog] by default. You can install Icarus on Debian/Ubuntu with:

    $ apt-get install iverilog

[Icarus Verilog]: https://steveicarus.github.io/iverilog/

More extensive testing is available in the `testsuite` subdirectory.
Additional requirements for running those tests are listed in the
[testsuite README].

[testsuite README]: testsuite/README.md

The `install-doc` target builds PDF documentation from LaTeX source files
that rely on a few standard style files.  The following Debian/Ubuntu
packages install sufficient tools to build the documentation:

    $ apt-get install \
        texlive-latex-base \
        texlive-latex-recommended \
        texlive-latex-extra \
        texlive-font-utils \
        texlive-fonts-extra

## Clone the repository

Clone this repository by running:

    $ git clone --recursive https://github.com/B-Lang-org/bsc

That will clone this repository and all of the submodules that it depends on.
If you have cloned the repository without the `--recursive` flag, you can setup
the submodules later with a separate command:

    $ git clone https://github.com/B-Lang-org/bsc
    $ git submodule update --init --recursive

## Build the BSC toolchain

At the root of the repository:

    $ make install-src

This will create a directory called `inst` containing an installation of the
compiler toolchain. This `inst` directory can later be moved to another
location; the tools do not hard-code the install location.

If you wish, you can install into another location by assigning the variable
`PREFIX` in the environment:

    $ make PREFIX=/opt/tools/bsc/bsc-<VERSION>

However, note that the `clean` target will delete the `PREFIX` directory!

An unoptimized, debug, or profiling build can be done using one of:

    $ make BSC_BUILD=NOOPT
    $ make BSC_BUILD=DEBUG
    $ make BSC_BUILD=PROF

You can provide the `-j` flag to `make` to specify the number of targets
to execute in parallel, however this does not control the parallelism of
the core haskell build.  To specify the number of modules that GHC may
compile in parallel, define `GHCJOBS` in the environment to that number:

    $ make GHCJOBS=4

### Optionally avoiding the compile of STP or Yices

The BSC tools expect to dynamically link with specific versions of STP and Yices,
found in `inst/lib/SAT/`.  By default, the build process will compile both
libraries and install them in that directory.  However, the BSC tools only need
one SMT solver; Yices is used by default, and STP can be selected via a flag.
Most users will never need to switch solvers, or even be aware of the option.
Thus, the build process offers the option of not compiling the STP library,
and instead installing a stub file, that the BSC tools will recognize and will
not allow the user to select that solver.  This option is chosen by assigning
a non-empty value to `STP_STUB`:

    $ make STP_STUB=1

This can be used if STP does not build on your system or if you want to avoid
the work of building the library.  A similar `YICES_STUB` option exists, for
skipping the build of the Yices library:

    $ make YICES_STUB=1

The BSC tools do need at least one SMT solver, so only one of these options
should be used.

## Test the BSC toolchain

The following command will run a smoke test to ensure the compiler and
simulator work properly:

    $ make check-smoke

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

    $ make install-doc

This will install into the same `inst` or `PREFIX` directory.
The installed documents include the [BSC User Guide]
and the [BSC Libraries Reference Guide].

[BSC User Guide]: https://github.com/B-Lang-org/bsc/releases/latest/download/bsc_user_guide.pdf
[BSC Libraries Reference Guide]: https://github.com/B-Lang-org/bsc/releases/latest/download/bsc_libraries_ref_guide.pdf

## Building a release

The Makefile provides a single target, `release`, that will perform the above
steps (of building the tools and the docs) and will also install a few
additional files, creating a complete release in the `inst` directory:

    $ make release

The additional files include a README, copyright and licensing info, and
release notes.  The release notes are written in [AsciiDoc](https://asciidoc.org/)
format that is published to HTML and PDF format using the
[Asciidoctor](https://asciidoctor.org/) tool, which is therefore a requirement
for building a release.

If you do not have Asciidoctor or would prefer not to install it (and all of
its dependencies), you can set `NOASCIIDOCTOR` in the environment:

    $ make NOASCIIDOCTOR=1 release

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

    $ export PATH=$(pwd)/inst/bin:$PATH

> **NOTE**: Earlier versions of BSC required that the environment variable
> `BLUESPECDIR` be set to point into the installation directory; this is no
> longer necessary, as the executables will figure out their location and
> determine the installation location on their own.

Run the following to see command-line options on the executable:

    $ bsc -help

Additional flags of use to developers can be displayed with the
following command:

    $ bsc -help-hidden

More details on using BSC, Bluesim, and Bluetcl can be found in the
[BSC User Guide] (built in this repository).
For language documentation and learning materials, see the
[Documentation section of the README](./README.md#documentation).

## Editors
Support for various editors for bs/bsv sources as well as language server support for the haskell sources for the bluespec compiler can be found in [./util](./util)
