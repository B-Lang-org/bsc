# BSC - Bluespec Compiler

See COPYING for copyright and license details.

This is a compiler, simulator, and associated tools for Bluespec
High Level Hardware Design Language (HL-HDL), supporting the two
optional syntaxes, BSV and BH.  Language specifications and
tutorials are available in the
[BSVlang repository](https://github.com/BSVLang/Main).

This respository contains:

- Source code for building the core compiler (`bsc`)
  - With front ends for BSV and BH syntax
  - With back ends for Verilog and Bluesim (C++ simulation)
- Source code for a BSC-aware Tcl/Tk shell (`bluetcl` and `bluewish`)
  - With commands to load BSC databases, for querying source code and elaborated designs
  - With commands for loading and running Bluesim simulations
- Standard Bluespec libraries
- Smoke test
- Utilities such as BSV-modes for emacs/gvim/jedit

More will be made available in the future (either here or in a sibling repo),
such as:

- Test suite
- Documentation (User Guide)
- Additional libraries

We welcome your feedback, issue reports, and pull requests.

----------------------------------------------------------------

### Downloading pre-built BSC tools

Pre-built packages will be available for download under the *Packages*
tab.

----------------------------------------------------------------

### How to build the BSC tools

The source code for BSC supports building on Linux and MacOS.
It may compile for other flavors of Unix, but likely will need
additional if/else blocks in source code or Makefiles.

The core of BSC is written in Haskell, with some libraries in C/C++.

#### Install the Haskell compiler (GHC)

You will need the standard Haskell compiler `ghc` which is available
for Linux, MacOS and Windows, along with some additional Haskell libraries.
These are available as standard packages in most Linux distributions.
For example, on Debian and Ubuntu systems, you can say:

        $ apt-get  install  ghc
        $ apt-get  install  libghc-regex-compat-dev  libghc-syb-dev  libghc-old-time-dev

The second command will install the Haskell libraries `regex-compat`,
`syb`, and `old-time`, as well as some libraries that they depend on.

You can do the analogous package-install on other
Linux distributions using their native package mechanisms, and use
Macports on Apple OS X.  Full details can be found at
[haskell.org](https://www.haskell.org/).  On some systems, you may
need to use the `cabal` command to install Haskell libraries:

        $ apt-get  install  cabal-install
        $ cabal  install  regex-compat  syb  old-time

The version of GHC should not matter, since the source code has been
written with extensive preprocessor macros, to support nearly every
minor release since as far back as 6.12 and earlier.  BSC builds with
the latest version at the time of this writing, which is 8.8.2.

#### Additional requirements

For building the Bluespec Tcl/Tk shell, you will need the fontconfig
and Xft libraries:

        $ apt-get  install  libfontconfig1-dev  libxft-dev

Building BSC also requires standard Unix shell and Makefile utilities.

The repository for
[the Yices SMT Solver](https://github.com/SRI-CSL/yices2)
is cloned as a submodule of this repository.  Building the BSC
tools will recurse into this directory and build the Yices library
for linking into BSC and Bluetcl. Yices may have its own requirements.
Yices currently requires the gperf perfect hashing library to compile:

        $ apt-get  install  gperf

Building the BSC tools will also recurse into a directory for the STP
SMT solver.  This is currently an old snapshot of the STP source code,
including the code for various libraries that it uses.  In the future,
this may be replaced with a submodule instantiation of the repository
for [the STP SMT solver](https://github.com/stp/stp).  When that
happens, additional requirements from that repository will be added.

#### Get the repository

Clone this repository by running:

        $ git  clone  --recursive  https://github.com/B-Lang-org/bsc

That will clone this respository and all of the submodules that it
depends on.
If you have cloned the repository without the `recursive` flag,
you can setup the submodules later with a separate command:

        $ git  clone  https://github.com/B-Lang-org/bsc
        $ git  submodule  update  --init  --recursive

#### Make the BSC tools

At the top directory of the repository, you can give the following command:

        $ make

This will create a directory called `inst` containing an installation
of the BSC tools.  This `inst` directory can later be moved to another
location; the tools do not hard-code the install location.

If you wish, you can install into another location by assigning the
variable `PREFIX` in the environment:

        $ make  PREFIX=/tools/bluespec

#### Smoke test

A cursory test is provided to ensure that the BSC tools are installed
and can be run.  The test runs BSC to compile a basic design into
both Verilog and Bluesim simulations and then tests that those
simulations run and produce the expected output.  Use the following
commands to execute the smoke test:

	 $ cd examples/smoke_test/
	 $ make smoke_test

For the Verilog simulation, by default it builds with IVERILOG (Icarus
verilog compiler), a free and open-source Verilog simulator, which you
can install with:

         $ apt-get  install  iverilog

Alternatively, the Makefile shows how you can point it at other
Verilog simulators such as VCS and VCSI (Synopyss), NCVERILOG and
NCSIM (Cadence) and MODELSIM (Mentor), and CVC.

Many people also routinely use VERILATOR to compile and simulate
bsc-generated Verilog.

----------------------------------------------------------------

### Running BSC

The installation contains a `bin` directory.  To run the BSC tools,
you only need to add the `bin` directory to your path (or provide that
path on the command line).  The executables in that directory will
expect to find other files in sibling directories within that same
parent installation directory.

Earlier versions of BSC required that the environment variable
BLUESPECDIR be set to point into the installation directory; this is
no longer necessary, as the executables will figure out their location
and determine the installation location on their own.

Run the following to see command-line options on the executable:

        $ bsc -help

Additional flags of use to developers can be displayed with the
following command:

        $ bsc -help-hidden

More details on using BSC, Bluesim, and Bluetcl can be found in the
User Guide [forthcoming].  Training and tutorials can be found in the
[BSVlang repository](https://github.com/BSVLang/Main).

----------------------------------------------------------------
