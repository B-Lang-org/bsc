<div class="title-block" style="text-align: center;" align="center">

# Bluespec Compiler

![Version] [![Build Status]](https://github.com/b-lang-org/bsc/actions?query=workflow%3ACI+event%3Apush)

[![Documentation]][Doc page]
[![License]](./COPYING)

[Doc page]:       https://github.com/B-Lang-org/bsc
[Documentation]:  https://img.shields.io/badge/docs-Manual-orange.svg?logo=markdown
[License]:        https://img.shields.io/badge/license-BSD%203-blueviolet.svg
[Version]:        https://img.shields.io/badge/release-2020.02,%20"Open%20Source%20Release"-red.svg?logo=v
[Build Status]:   https://github.com/b-lang-org/bsc/workflows/CI/badge.svg?branch=master&event=push

<strong>
  <a href="https://github.com/B-Lang-org/bsc">Homepage</a>&nbsp;&nbsp;&bull;&nbsp;&nbsp;<a href="https://github.com/B-Lang-org/bsc">Get Started</a>
</strong>

---

</div>

Compiler, simulator, and tools for the **Bluespec Hardware Description
Language**. Bluespec is a single language for hardware designs that comes in
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

> **NOTE**: The current release is minimal, and more code will
> be made available in the future, including:
>
> - Documentation (User Guide)
>
> The repository is still evolving. We welcome your feedback, issue reports,
> and pull requests.

A separate repository, [bsc-contrib],
exists for sharing libraries and utilities that don't (or don't yet) belong in
the core tools.

Tests and testing infrastructure are provided in a separate
[bsc-testsuite] repository.

A graphical environment for using BSC is available in a separate [bdw]
repository. BDW (the BSC Development Workstation) provides a number of
tools, including the ability to view simulation waveforms as
source-level values.

[Bluespec Inc]: https://bluespec.com
[Flute]: https://github.com/bluespec/Flute
[Piccolo]: https://github.com/bluespec/Piccolo
[Shakti]: https://shakti.org.in

[bsc-contrib]: https://github.com/B-Lang-org/bsc-contrib
[bsc-testsuite]: https://github.com/B-Lang-org/bsc-testsuite
[bdw]: https://github.com/B-Lang-org/bdw

---

## Compiling BSC from source

Binaries for the Bluespec toolchain are currently unavailable, so you must
build them from source code. The source code can currently be built on Linux
and MacOS. It may compile for other flavors of Unix, but likely will need
additional if/else blocks in source code or Makefiles.

The core of BSC is written in Haskell, with some libraries in C/C++.

### Install the Haskell compiler (GHC)

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


Bluespec compiler builds are tested with GHC 7.10.1 and greater, and older
GHC releases are not supported.

Beyond that, any version up to 8.10.1 (the latest at the time of writing) will
work, since the source code has been written with extensive preprocessor macros
to support every minor release since.

### Additional requirements

For building and using the Bluespec Tcl shell (`bluetcl`),
you will need the `tcl` library:

    $ apt-get install tcl-dev

Building BSC also requires standard Unix shell and Makefile utilities.

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

The `check` target runs a test using an external Verilog simulator, which is
[Icarus Verilog] by default. You can install Icarus on Debian/Ubuntu with:

    $ apt-get install iverilog

[Icarus Verilog]: http://iverilog.icarus.com

### Clone the repository

Clone this repository by running:

    $ git clone --recursive https://github.com/B-Lang-org/bsc

That will clone this repository and all of the submodules that it depends on.
If you have cloned the repository without the `--recursive` flag, you can setup
the submodules later with a separate command:

    $ git clone https://github.com/B-Lang-org/bsc
    $ git submodule update --init --recursive

### Build and test the toolchain

At the root of the repository:

    $ make all
    $ make check

This will create a directory called `inst` containing an installation of the
compiler toolchain. It will then run a smoke test to ensure the compiler and
simulator work properly. This `inst` directory can later be moved to another
location; the tools do not hard-code the install location.

If you wish, you can install into another location by assigning the variable
`PREFIX` in the environment:

    $ make PREFIX=/tools/bluespec

An unoptimized, debug, or profiling build can be done using one of:

    $ make BSC_BUILD=NOOPT
    $ make BSC_BUILD=DEBUG
    $ make BSC_BUILD=PROF

For more extensive testing, see the [bsc-testsuite] repository.

#### Choosing a Verilog simulator

The Makefile in `examples/smoke_test` shows how you can point the default
`check` target at other Verilog simulators such as VCS and VCSI (Synopys),
NC-Verilog & NCsim (Cadence), ModelSim (Mentor), and CVC.

Many people also use [Verilator][] to compile and simulate `bsc`-generated
Verilog -- but you must write your own C++ harness for your design in order to
use it.

[Verilator]: https://www.veripool.org/wiki/verilator

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
(forthcoming). Training and tutorials can be found in the [BSVlang
repository](https://github.com/BSVLang/Main).

---

## License

The Bluespec toolchain is available under the BSD license. The source code also
includes several other components under various license agreements (all of it
open/copyleft software). See `COPYING` for copyright and license details.
