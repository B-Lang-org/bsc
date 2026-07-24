// False-collapse candidate: primBuildModule forced inside another
// primBuildModule's rule body.  Outer frame: ns = ["outerHist"] (singleton,
// tail []), elabProgress = Just (EPRule shift), no rules registered yet.
// Inner (ProbeWire keepType) pushes ns = ["x"] (singleton, tail []).
// Equal (empty) tails + no rules => collapse renames the outer frame and
// DROPS its rule progress.
// Pattern copied from SVA.bsv valueFunctionSVA / ProbeWire.bsv keepType,
// both of which use the exported Prelude primitive primBuildModule.

import ProbeWire::*;

function Bool nestedProbe(Reg#(Bool) r);
   let c = clockOf(r);
   let rst = noReset;
   let v = primBuildModule(primGetName(outerHist), c, rst,
      module#(Bool);
         Bool cur = r;
         Reg#(Bool) q <- mkRegU;
         rule shift;
            q <= keepType(cur);
         endrule
         return q;
      endmodule);
   return v;
endfunction

(* synthesize *)
module sysNestedBuildModule(Empty);
   Reg#(Bool) sig <- mkReg(False);
   Reg#(Bool) dst <- mkReg(False);
   rule consume;
      dst <= nestedProbe(asReg(sig));
   endrule
endmodule
