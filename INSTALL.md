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

    $ mkdir -p /opt/tools/bsc
    $ mv inst /opt/tools/bsc/bsc-4.0.0
    $ cd /opt/tools/bsc
    $ ln -s bsc-4.0.0 latest

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

Bluespec compiler builds are tested with GHC 8.0.2 and greater.
GHC releases older than 7.10.1 are not supported.

Beyond that, any version up to 8.10.1 (the latest at the time of writing) will
work, since the source code has been written with extensive preprocessor macros
to support every minor release since.

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
Bluetcl. Yices currently requires `autoconf` and the `gperf` perfect hashing
library to compile:

    $ apt-get install \
        autoconf \
        gperf

Building the BSC tools will also recurse into a directory for the STP SMT
solver. This is currently an old snapshot of the STP source code, including the
code for various libraries that it uses. In the future, this may be replaced
with a submodule instantiation of the repository for [the STP SMT
solver](https://github.com/stp/stp). When that happens, additional requirements
from that repository will be added. The current snapshot requires Perl, to
generate two source files. It also needs flex and bison:

    $ apt-get install flex bison

The `check-smoke` target runs a test using an external Verilog simulator, which is
[Icarus Verilog] by default. You can install Icarus on Debian/Ubuntu with:

    $ apt-get install iverilog

[Icarus Verilog]: http://iverilog.icarus.com

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

## Build and test the toolchain

At the root of the repository:

    $ make install-src
    $ make check-smoke

This will create a directory called `inst` containing an installation of the
compiler toolchain. It will then run a smoke test to ensure the compiler and
simulator work properly. This `inst` directory can later be moved to another
location; the tools do not hard-code the install location.

If you wish, you can install into another location by assigning the variable
`PREFIX` in the environment:

    $ make PREFIX=/opt/tools/bsc/bsc-<VERSION>

However, note that the `clean` target will delete the `PREFIX` directory!

An unoptimized, debug, or profiling build can be done using one of:

    $ make BSC_BUILD=NOOPT
    $ make BSC_BUILD=DEBUG
    $ make BSC_BUILD=PROF

For more extensive testing, see the [testsuite README](testsuite/README.md)
in the `testsuite` subdirectory.

### Choosing a Verilog simulator

The Makefile in `examples/smoke_test` shows how you can point the default
`check-smoke` target at other Verilog simulators such as VCS and VCSI (Synopys),
NC-Verilog & NCsim (Cadence), ModelSim (Mentor), and CVC.

Many people also use [Verilator][] to compile and simulate `bsc`-generated
Verilog -- but you must write your own C++ harness for your design in order to
use it.

[Verilator]: https://www.veripool.org/wiki/verilator

## Build documentation

To build and install the PDF documentation, you can add the following:

    $ make install-doc

This will install into the same `inst` or `PREFIX` directory.
The installed documents include the BSC User Guide and the BSC Libraries
Reference Guide.

## Building a release

The Makefile provides a single target, `release`, that will perform the above
steps (of building the tools and the docs) and will also install a few
additional files, creating a complete release in the `inst` directory.
The additional files include a README, copyright and licensing info, and
release notes.  The release notes are written in [AsciiDoc](https://asciidoc.org/)
format that is published to HTML and PDF format using the
[AsciiDoctor](https://asciidoctor.org/) tool, which is therefore a requirement
for building a release.

## Exporting the source code

If you wish to make a snapshot of the source code available, outside of
Git, there are some steps you will need to take in the `src/comp/` directory.
The build in that directory uses Git to automatically generate the version
information for the compiler and place it in the file `BuildVersion.hs`.
If you are exporting the code, you will want pre-generate this file and then
adjust the Makefile to not rebuild it.  That can be done by changing the
assignment of `NOUPDATEBUILDVERSION` to `1`, in the Makefile.

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

More details on using BSC, Bluesim, and Bluetcl can be found in the User Guide
(built in this repository).
Language documentation, training, and tutorials can be found in the
[BSVlang repository](https://github.com/BSVLang/Main).
