import FixNameMid::*;

// mid is inlined (not synthesized), so its internal rule "poison"
// bubbles up into sysFixNameDeferred's scope.  The descending_urgency attribute
// references the bubbled rule name, forcing a lookup in the poisoned
// name map (checkAddRulesAttributes -> M.lookup), which forces the
// remIStateLocPrefix computation over the collapsed (renamed) frame.

(* synthesize *)
(* descending_urgency = "drive, mid_z_poison" *)
module sysFixNameDeferred(Empty);
   Reg#(Bool) t <- mkReg(False);
   Reg#(Bool) mid <- mkMid;
   rule drive;
      t <= mid;
   endrule
endmodule
