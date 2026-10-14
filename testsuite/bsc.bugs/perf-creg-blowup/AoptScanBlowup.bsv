// Regression test for the AExpand.aoptExpandTest quadratic.
//
// Many submodule instance vars + many local defs.  The pre-fix version
// of aoptExpandTest recomputes aVars(sss) and does linear elem on it
// on every call, giving O(#defs * #vars) cost.  At this scale the aopt
// phase is ~10x slower without the sinstVars Set fix.
//
// Needs +RTS -K3G -RTS due to the size of the submodule pool causing
// stack pressure in upstream passes (eqPtrs, scheduler tsort, etc.).
package AoptScanBlowup;

import Vector::*;

typedef 8192 NConsts;
typedef 512  NRules;
Integer chainDepth = 128;
typedef 32 Width;

(* synthesize *)
module mkAoptScanBlowup (Empty);

   Vector#(NConsts, Reg#(Bit#(Width))) consts <- replicateM(mkReg(0));
   Vector#(NRules,  Reg#(Bit#(Width))) states <- replicateM(mkReg(0));

   Reg#(Bool) inited <- mkReg(False);
   rule initconsts (!inited);
      for (Integer c = 0; c < valueOf(NConsts); c = c + 1)
         consts[c] <= fromInteger(c);
      inited <= True;
   endrule

   for (Integer r = 0; r < valueOf(NRules); r = r + 1) begin
      rule step (inited);
         Bit#(Width) acc = states[r];
         for (Integer k = 0; k < chainDepth; k = k + 1) begin
            Integer idx = (r * (k + 1) + 7 * k + 3) % valueOf(NConsts);
            Bit#(Width) x = consts[idx];
            if (k % 4 == 0) acc = acc + x;
            else if (k % 4 == 1) acc = acc ^ (x << 1);
            else if (k % 4 == 2) acc = acc - (x | 'h55);
            else acc = (acc + x) ^ (x - acc);
         end
         states[r] <= acc;
      endrule
   end

endmodule

endpackage
