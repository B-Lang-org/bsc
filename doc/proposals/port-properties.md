# Proposal: Semantic Port Properties

Status: draft for discussion.
Implementation: `getIOPropsA` in `src/comp/VIOProps.hs` (on this branch),
exposed by the dump flag `-dAPackageIOproperties` alongside the existing
`-dIOproperties`.

## Problem

BSC annotates every port of a generated module with properties -- `clock`,
`reset`, `reg`, `const`, `unused`, `inhigh`, ... -- which appear in the
"Ports:" comment of the generated Verilog and, more importantly, in the
import-BVI wrapper recorded in the `.bo` file, where they become the
*declared* port properties of the module when a parent instantiates it.
Parents consume them for their own property deduction, for `always_enabled`
legality (`inhigh`), and for readiness reasoning (`const`).

Today these properties are computed by `getIOProps`, which runs at the very
end of the Verilog backend and *measures the optimized netlist*.  That
definition has three structural problems:

1. **The properties depend on which optimizations ran.**  A ready signal
   is labeled `const` if (and only if) `aOpt`'s rewriting happened to fold
   it; an input is `unused` only if its uses were syntactically direct; an
   unused input clock loses its `clock` label because no surviving netlist
   connection witnesses it.  Whether a port "is registered" should be a
   fact about the design, but today it is a fact about a particular
   compile.  Because the properties feed parent compiles through the
   `.bo`, this instability propagates up the hierarchy: what a parent may
   assume about a child changes when the child is recompiled with
   different settings.

2. **The properties depend on where module boundaries fall.**  With
   `-no-inline-rwire`, a value read through a bypass wire loses its `reg`
   label -- although an RWire's Verilog is `assign WGET = WVAL`, and the
   value is connected to the same register either way.

3. **Only the Verilog backend has them.**  `getIOProps` needs the final
   `ASPackage`, so Bluesim-only compiles record no port properties at all
   (a long-standing `XXX` in `bsc.hs`).

## Proposal

Define each port property *denotationally* -- by what it means for the
hardware described by the elaborated design and its schedule -- and compute
the properties by a conservative analysis of the `APackage`, independent of
the backend pipeline.  A property is asserted only when it is entailed by
structure, dataflow, and the schedule; never by which optimizations the
backend performs or by where module boundaries fall among wiring
primitives.

The definitions:

* **`clock`, `clock gate`, `reset`, `inout`** (and declared properties such
  as `inhigh`/`outhigh`): the structural role of the port in the module's
  interface.  These are facts of the interface, not deductions, and are
  always present -- an unused input clock is `clock unused`.

* **`reg`**: the port's value is the registered output of a state element
  (output ports), or feeds only the data inputs of state elements (input
  ports), reached through *wiring only*: concatenation, extraction,
  definitions, and the wiring primitives.  RWire/BypassWire/CReg instances
  are looked through regardless of the inlining flags, because the
  primitive is connected to the same things whether or not it is inlined.
  The strictness matters: a boundary mux breaks the property, so `reg` on
  both directions is exactly the flop-in/flop-out condition needed to
  isolate timing at physical-design block boundaries.

* **`const`**: the port's value is entailed to be constant by the design
  and its schedule.  Source-level constants are already folded by the
  evaluator during elaboration; what this analysis adds is the folding of
  *schedule-time* facts, which do not exist until after scheduling:
  `WILL_FIRE`s that the schedule makes constant (rules that can never
  fire, or always fire), the validity of wires that are never or always
  set, selections whose conditions become constant, and mux arms that win
  or lose the arbitration outright (modeled with the same port
  allocation, exclusivity test, and earliness order that `AState` uses).

* **`unused`**: the port drives no hardware.  Uses that exist only in
  simulation (arguments of foreign function and task calls) do not count;
  neither does a use by logic that is itself unused, by a rule that can
  never fire, or by a mux arm that loses the arbitration.

**Soundness contract:** the analysis is a conservative under-approximation
of the definitions.  It may fail to assert a property whose truth requires
reasoning it does not perform (see Limitations); it never asserts a
property that does not hold of the hardware.

**Stability contract:** recompiling the same design with different
optimization or inlining settings, or with a different backend, yields the
same properties.

**Where deduction stops -- agreement, not enumeration.**  The analysis
propagates *expressions* through wires (values, properties, and boolean
structure all cross wire and CReg boundaries, so a tautology carried
through a wire is still recognized), and it crosses merge points (muxes,
multiple setters) exactly when all arms carry the same expression -- which
is a structural fact, and matches AState's own collapsing of
equal-expression mux arms.  It deliberately does not reason by
*enumerating* the values that reach a merge: a wire set to 1, 2, or 3 on
different paths is not deduced to be "greater than 0", because that
property comes from the particular values written, not from the structure
of the design -- change one constant and it silently vanishes.  Properties
that brittle are exactly what the stability contract excludes from the
interface metadata.

## Evidence

The implementation was validated by compiling every synthesizable design in
the testsuite (2841 candidate files; 2124 reach code generation standalone)
with both analyses and comparing the dumps: about 18,300 port lines.

* No internal errors; the port enumeration (names, directions, sizes,
  order) matches `getIOProps` on every module.
* ~1,575 lines differ because the new analysis keeps structural labels the
  netlist measurement loses (`reset unused` vs `unused`, `clock` on
  passthrough or unused clocks, `reg` on CReg port-0 reads -- which
  `getIOProps` misses only because the CReg import does not declare the
  property on `Q_OUT_0`).
* 5 lines differ because `unused` here propagates through dead logic that
  `getIOProps` only traces through direct connections (signals feeding a
  `$display` through arithmetic).
* An argument inout fed through to an interface inout is one net exposed
  at two pins; `getIOProps` labels the argument pin `unused` as an
  artifact of the alias collapse, while this analysis reports both pins
  as live.
* 110 lines are properties `getIOProps` finds and this analysis does not,
  in four categories: enables whose method effects die inside *value*-
  method argument muxes (49, closable with the same arbitration model
  already applied to action methods); values simplified only by deeper
  boolean rewriting (33 + 9, see Limitations); inout nets traced through
  `InoutConnect` (19).
* No line asserts a property that `getIOProps` contradicts.

Stability was demonstrated directly: under `-no-inline-rwire` /
`-no-inline-creg` the new analysis reports identical properties while
`getIOProps` drops `reg`/`const` labels; `-keep-fires` changes neither.

The full dejagnu testsuite was also run with this branch (855 test
groups, ~18,000 checks): no failures attributable to the change (the
only failing tests are ones which cannot run in the build container --
SystemC linking, and tests requiring unreadable files while running as
root).

The analysis is memoized per definition (lazy maps for the evaluator,
the output properties, and the input uses), so each definition is
analyzed at most once and the cost is near-linear in the package size.
On the largest testsuite design (the h264 deblocking filter, ~13s to
compile), forcing the analysis is not measurable above compile-time
noise, and the full-testsuite sweep forced it on all 2124 designs with
no timeouts.

Golden tests covering each mechanism (wires, CRegs, schedule facts,
split-method readies, arbitration, foreign calls) are checked in under
`testsuite/bsc.verilog/portprops/APkgProps_*`, dumping both analyses side
by side.

On the portprops testsuite directory specifically, the categories above
account for every difference: of the 33 compiling designs, 18 match
`getIOProps` byte-for-byte, 13 differ only by the retained structural
labels, 1 (`InoutProps_ArgToIfc`) is the inout alias-collapse artifact,
and 1 (`APkgProps_DeadLogic`) is the dead-logic `unused` difference.
Covering that directory under this proposal is therefore a golden-file
regeneration (migration step 3), not an analysis change.

The directory now exercises each deduction mechanism: value/const/reg
output deduction with concats and extractions, input joins with unused
filtering, inhigh, argument and interface inouts (including BVI), the
module's own and submodule-derived clock/gate/reset ports, wire and CReg
look-through, schedule facts (never/always-firing rules), split-method
readies, arbitration wins and losses as well as surviving muxes, foreign
calls, dead-logic unusedness, and parameter exclusion.

## How narrow is the optimizer's edge?

The 42 "deeper rewriting" lines invite the question: how often can a
syntactic optimization expose a property that the semantic analysis cannot
see?  Constructing such a case deliberately turns out to be hard.  Of six
adversarial attempts, five failed: user-written tautologies, redundant
nested selections, and absorption shapes are all folded by the front-end
evaluator during elaboration and never reach the netlist; reassembled
extractions and schedule-constant residues are covered semantically.  The
single surviving shape is two-level boolean minimization over dynamic
leaves -- `(a && b) || (!a && b) == b` -- which requires knowingly writing
a redundant guard (or generated/split condition code; the testsuite's two
real instances are both of this species).  If those properties are ever
wanted, the stable way to obtain them is a bounded validity check
(truth-table evaluation of 1-bit guards over their dynamic leaves), which
is semantic and optimizer-independent -- not a re-implementation of the
optimizer.  This proposal deliberately does not promise them: a `const`
that exists because of a particular rewrite is exactly the instability
being removed.

## Migration

1. **(done, this branch)** The analysis exists behind
   `-dAPackageIOproperties`; golden tests compare both analyses.
2. Feed the wrapper attributes (`veriPortProps` in `bsc.hs`) and the
   Verilog "Ports:" comment from the new analysis, behind a flag,
   default off.  Bluesim compiles gain port properties in their `.bo`s
   for free (the analysis needs only the `APackage` and the schedule).
3. Run the full testsuite with the flag on.  Expected churn: golden
   Verilog files' "Ports:" comments change where the new labels are
   richer; behavioral differences in parent compiles are confined to the
   110 known lines and should be reviewed (the main risk is a parent
   asserting `always_ready` against a child whose RDY `const` was
   optimizer-derived -- two designs in the testsuite exhibit the
   pattern, neither with such a parent).
4. Default the flag on for a release, keeping `getIOProps` and the old
   dump available for comparison.
5. Remove `getIOProps`.

## Limitations (known, documented in the module)

* Boolean minimization of guards over dynamic values (above).
* Value analysis of register contents (a never-written `mkReg(0)` is not
  `const`).
* Inout nets are not traced through `InoutConnect` instances.
* Value-method argument muxes are not yet arbitration-modeled (the 49
  enable lines); same machinery as action methods, planned.

## Enabled by this (future work, not in this proposal)

* **Flop-in/flop-out boundary checking** for physical-design blocks: a
  per-module pragma requiring every port to be `reg` (or `const`/`unused`/
  structural), replacing an external synthesis run for boundary timing
  isolation.  The strict `reg` definition above is exactly the needed
  predicate, and `always_enabled`/`always_ready` remove the EN/RDY pins
  that would otherwise violate it.
* **Boundary registration report** joining the properties with
  `VPathInfo` (also computed semantically, by `aPaths`): per port,
  `registered` / `registered-through-logic` / `feedthrough`.
* Port properties for Bluesim-compiled modules (step 2 above).
* Consistent CReg primitive imports (declaring `reg` on `Q_OUT_0` would
  let the netlist measurement agree; the semantic analysis does not need
  it).

## Open questions

1. Should the Verilog "Ports:" comment show the richer structural labels
   (churn in checked-in golden Verilog), or should the comment be kept
   minimal while the `.bo` attributes carry the full set?
2. Should the optimizer-derived `const`s be preserved during migration
   via the bounded validity check, or dropped as proposed?
3. Naming: the dump flag, and whether `getIOPropsA` simply becomes
   `getIOProps` at step 5.
