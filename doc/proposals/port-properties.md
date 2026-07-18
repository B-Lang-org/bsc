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
with both analyses and comparing the dumps: about 18,300 port lines, of
which 1,686 differ.

* No internal errors; the port enumeration (names, directions, sizes,
  order) matches `getIOProps` on every module.
* 1,638 lines differ because the new analysis keeps structural labels the
  netlist measurement loses (`reset unused` vs `unused`, `clock` on
  passthrough or unused clocks, inout roles).
* 15 lines are properties this analysis finds and `getIOProps` does not:
  `unused` propagating through dead logic that `getIOProps` only traces
  through direct connections (5), and `reg` on values which are
  registered but which the netlist does not show as a direct register
  connection -- CReg port-0 reads (the CReg import does not declare the
  property on `Q_OUT_0`), and a register value repacked through an
  identity case statement which the optimizer leaves behind but the
  agreement rule sees through.
* An argument inout fed through to an interface inout is one net exposed
  at two pins.  `getIOProps` used to label the argument pin `unused` --
  not from analysis, but because the interface-inout definitions were
  missing from its use map -- and the mislabel propagated up parent
  compiles (19 lines in the sweep).  The fix to `getIOProps` itself
  landed separately (B-Lang-org/bsc PR 1057, on which this branch is
  based): both passes now report both pins as live.
* 33 lines are properties `getIOProps` finds and this analysis does not,
  all in the one remaining category: values whose simplification
  requires boolean minimization over independent dynamic guards (the
  principled boundary -- see below).  Earlier drafts had two more
  categories, both now closed.  Enables whose method effects die inside
  value-method argument muxes (49 lines): the argument muxes of value
  methods are arbitration-modeled like those of action methods (with
  RDY-based selectors for interface value-method users), and the
  references AState itself creates for a caller's WILL_FIRE are folded
  semantically (a port enable absorbed by a constant or complementary
  conjunct; the selector of a direct connection, a losing arm, or a
  mux's last arm, which the don't-care default absorbs).  And the inout
  alias lines (19), resolved in `getIOProps`'s favor of accuracy as
  above.
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
account for every difference: of the 35 compiling designs, 18 match
`getIOProps` byte-for-byte, 16 differ only by the retained structural
labels (including `InoutProps_ArgToIfc`, whose argument-pin mislabel is
fixed in `getIOProps` on this branch), and 1 (`APkgProps_DeadLogic`) is
the dead-logic `unused` difference.

The directory now exercises each deduction mechanism: value/const/reg
output deduction with concats and extractions, input joins with unused
filtering, inhigh, argument and interface inouts (including BVI), the
module's own and submodule-derived clock/gate/reset ports, wire and CReg
look-through, schedule facts (never/always-firing rules), split-method
readies, arbitration wins and losses as well as surviving muxes -- for
action methods and for value methods (including RDY-selected uses by
interface value methods), the folding of enable and selector references
(complementary enables, losing arms, last arms), foreign calls,
dead-logic unusedness, and parameter exclusion.

## How narrow is the optimizer's edge?

The "deeper rewriting" lines invite the question: how often can a
syntactic optimization expose a property that the semantic analysis cannot
see?  Constructing such a case deliberately turns out to be hard.  Of six
adversarial attempts, five failed: user-written tautologies, redundant
nested selections, and absorption shapes are all folded by the front-end
evaluator during elaboration and never reach the netlist; reassembled
extractions and schedule-constant residues are covered semantically.
Hiding a foldable shape behind a wire does not work either, since the
analysis propagates expressions through wires (a tautology whose negated
half arrives through an RWire is still recognized; see
`APkgProps_WireExpr`).

What survives is exactly what the "agreement, not enumeration" rule
excludes on principle:

* boolean identities relating two or more *independent* dynamic values --
  `(a && b) || (!a && b) == b` -- i.e. two-level minimization, which
  requires knowingly writing a redundant guard (the testsuite's real
  instances are generated/split condition code); and
* value enumeration at merges (the wire set to 1, 2, or 3 above).

So the optimizer's edge is not an accident of what this analysis happens
to implement; it coincides with the semantic boundary this proposal
draws.  If minimization-derived properties are ever wanted, the stable
way to obtain them is a bounded validity check (truth-table evaluation
of 1-bit guards over their dynamic leaves), which is semantic and
optimizer-independent -- not a re-implementation of the optimizer.  This
proposal deliberately does not promise them: a `const` that exists
because of a particular rewrite is exactly the instability being
removed.

## Migration

1. **(done, this branch)** The analysis exists behind
   `-dAPackageIOproperties`; golden tests compare both analyses.
2. **(done, this branch)** The wrapper attributes (`veriPortProps` in
   `bsc.hs`) and the Verilog "Ports:" comment are fed from the new
   analysis, for every backend -- Bluesim compiles gain port properties
   in their `.bo`s (the analysis needs only the `APackage` and the
   schedule).  `getIOProps` remains, computed only when its comparison
   dump (`-dIOproperties`) is requested.
3. **(done, this branch)** Run the full testsuite.  The churn: golden
   Verilog files' "Ports:" comments change where the new labels are
   richer; behavioral differences in parent compiles are confined to
   the 33 known lines (the main risk is a parent asserting
   `always_ready` against a child whose RDY `const` was
   optimizer-derived -- two designs in the testsuite exhibit the
   pattern, neither with such a parent).
4. Keep `getIOProps` and its dump available for comparison for a
   release.
5. Remove `getIOProps`.

## Non-goals and pending work (documented in the module)

Excluded on principle (the "agreement, not enumeration" boundary):

* Boolean minimization of guards over independent dynamic values
  (above).
* Value enumeration at merges, and value analysis of register contents
  (a never-written `mkReg(0)` is not `const`): properties of the
  particular values written, not of the design's structure.

Pending (deducible under the contract, not yet implemented):

* Inout nets are not traced through `InoutConnect` instances: an inout
  reaching only a chain of connections that ends nowhere would still be
  reported live.  (Conservative; no design in the testsuite exercises
  it -- connection primitives there only join nets that have real
  endpoints.)

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
