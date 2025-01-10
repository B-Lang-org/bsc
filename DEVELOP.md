<div class="title-block" style="text-align: center;" align="center">

# Bluespec Compiler - Information for developers

---

</div>

Here you can find documentation on the internal architecture of [BSC](./README.md)
and other helpful information for people who want to contribute to the source code.

Feel free to ask questions on GitHub (in an Issue or a Discussion)
or on the [`bsc-dev`](https://groups.io/g/bsc-dev) mailing list.
The `bsc-dev` list is for questions that are only relevant to developers,
to keep traffic on the [`b-lang-discuss`](https://groups.io/g/b-lang-discuss)
mailing list light for people who are just users.

---

At the moment there is no formal documentation.
However, there are written responses to questions on GitHub and the mailing lists,
that can someday be collected and turned into a document.
The following is a running list of those writings.

### Basics / General info

* [BSC is a series of stages](https://groups.io/g/bsc-dev/message/14)
  * This write-up includes a link to the following (incomplete)
    [diagrams of the BSC stages](https://docs.google.com/document/d/1130fyOsPtS6gMppB6BaO-qVXxzO5b_ha7sXwLdd8Dtg/edit?usp=sharing)
  * See also [this brief breakdown of BSC](https://groups.io/g/b-lang-discuss/message/358)
    by its three internal representations (CSyntax, ISyntax, ASyntax)
  * Briefly on [printing and dumping from BSC and intermediate files](https://groups.io/g/b-lang-discuss/message/356)
* [More on the stages, the backend split, Bluesim stages, and the structure of Bluesim output](https://github.com/B-Lang-org/bsc/issues/743#issuecomment-2436483892)
* [The meaning of `.bo` and `.ba` files and compiler flow](https://github.com/B-Lang-org/bsc/discussions/575#discussioncomment-6458212)
* Hidden flags
  * BSC has a flag `-help-hidden` for developers,
    which shows more information than the `-help` for users
  * Like the LaTeX documentation for flags in the BSC User Guide,
    there is short LaTeX document for hidden flags at BS Inc (called `internal-user-guide`),
    which could become part of a BSC Developer Guide

### Compiling

* See [INSTALL.md](./INSTALL.md) for info on building and installing
* TBD: Any info on tools, dependencies, and compiling options
  * e.g. individual SMT libraries can be omitted using `STP_STUB=1` or `YICES_STUB=1`

### Testing

* See the test suite's own [README file](./testsuite/README.md)

### BSC stage: Parsing

* [Keyword parsing in BH/Classic](https://github.com/B-Lang-org/language-bh/issues/5#issuecomment-1856814271)

### BSC stage: Type checking

* See the link on the use of SMT solvers, below

### BSC stage: Elaboration

* [How to add a new evaluator primitive to BSC](https://groups.io/g/b-lang-discuss/message/526)
  * specifically how to add a function to get the current module name
* See the link on the use of SMT solvers, below

### BSC stage: Scheduling

* [Understanding scheduling](https://github.com/B-Lang-org/bsc/discussions/622#discussioncomment-7203579)
* See the link on the use of SMT solvers, below

### BSC backends / naming

* [Naming conventions in the generated Verilog](https://groups.io/g/b-lang-discuss/topic/106903347)
* [Verilog/Bluesim "main" and the naming of clock and reset ports](https://groups.io/g/b-lang-discuss/message/606)

### BSC backend: Verilog

* [BSC's deduction of portprops](https://groups.io/g/b-lang-discuss/topic/106516831)
* [How to use the different Verilog directories (for different synth tools)](https://groups.io/g/b-lang-discuss/topic/106402322)

### BSC backend: Bluesim

* See the link on Bluesim stages, above, under Basics
* [How Bluesim works (mostly the VCD dumping)](https://github.com/B-Lang-org/bsc/issues/519#issuecomment-1873853532)
* [How Bluesim provides implementations for import-BVI](https://groups.io/g/b-lang-discuss/topic/106520424)
* [How the Bluesim C API is imported into Bluetcl](https://groups.io/g/b-lang-discuss/message/554)
* There is a template for making Bluesim standalone programs (without Tcl) in `bsc/util/bsim_standalone/`

### Bluetcl

* [Support for reflection in BSC](https://groups.io/g/b-lang-discuss/message/513)
  * specifically, Bluetcl (outside the language) and Generics (inside the language)
* See the link on how Bluesim's C API is imported into Bluetcl, above, under Bluesim

### SMT solvers

* [The ways that SMT solvers are used in BSC](https://groups.io/g/b-lang-discuss/message/370)
* [SAT solver usage and dumping](https://github.com/B-Lang-org/bsc/discussions/693#discussioncomment-9148985)
* TBD: Status of the SMT solver source codes and how they are incorporated into BSC

### Clock and Reset methodology

* [Clock/reset inference](https://github.com/B-Lang-org/bsc/discussions/661)
* BSC implements certain design decisions for clocks and resets --
  for example, the choice to implement reset inside of state elements (to ignore the `EN` input)
  instead of outside (as part of the `RDY` logic) --
  and there may be some documentation (perhaps internal to BS Inc) on those decisions
  * There was a paper at MEMOCODE 2006,
    ["Reliable Design with Multiple Clock Domains"](https://www.researchgate.net/publication/224648422_Reliable_design_with_multiple_clock_domains)
    * An earlier version of this paper was submitted to DCC'06 (Designing Correct Circuits)
  * There is a BS Inc document from 16 Dec 2004 (`mcd.pdf`) that discusses some options, but only clocks, not yet reset
  * There is a BS Inc document from 28 Oct 2004 (`resets.txt`) that purports to be "a proposal on reset handling"
    but is very prelimary about the problem, not yet the solution
  * There is a BS Inc file `bsc-doc/doc/MCD-extensions.txt` that describes
    the new things in BSC to support MCD, both user visible attributes and
    the BSC source code changes
  * The BS Inc training slides include a
    [lecture on MCD](https://github.com/BSVLang/Main/blob/master/Tutorials/BSV_Training/Reference/Lec12_Multiple_Clock_Domains.pdf)

---
