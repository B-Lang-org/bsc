<div class="title-block" style="text-align: center;" align="center">

# Bluespec Compiler

[![Version]](https://github.com/B-Lang-org/bsc/releases/tag/2024.07)
[![License]](./COPYING)
[![Build Status]](https://github.com/b-lang-org/bsc/actions?query=workflow%3ACI+event%3Apush)

[License]:        https://img.shields.io/badge/license-BSD%203-blueviolet.svg
[Version]:        https://img.shields.io/badge/release-2024.07-red.svg?logo=v
[Build Status]:   https://github.com/b-lang-org/bsc/workflows/CI/badge.svg?branch=main&event=push

**[Community] &bull; [Download] &bull; [Documentation] &bull; [Build] &bull; [Test]**

[Community]: #community
[Download]: #download
[Documentation]: #documentation
[Build]: ./INSTALL.md
[TEST]: ./testsuite/README.md

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

## License

The Bluespec toolchain is provided by [Bluespec Inc] and
available under the BSD-3-Clause license.
The source code also includes several other components under
various license agreements (all of it open/copyleft software).
See [`COPYING`](COPYING) for copyright and license details.
