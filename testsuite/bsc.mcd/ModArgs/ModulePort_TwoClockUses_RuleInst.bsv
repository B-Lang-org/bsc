import Clocks::*;

(* synthesize *)
module sysModulePort_TwoClockUses_RuleInst #(Bit#(32) x)
                                            (Clock c2, Reset r2, Empty i);

   Reg#(Bit#(32)) rg1 <- mkReg(0);

   // This should impose a clock, derived from compiling the submod
   Empty s <- mkModulePort_TwoClockUses_RuleInst_Sub(x,
				                     clocked_by c2,
						     reset_by r2);

   rule r1;
      rg1 <= x;
   endrule

endmodule

// this should derive its clock
(* synthesize *)
module mkModulePort_TwoClockUses_RuleInst_Sub #(Bit#(32) x) ();

   Reg#(Bit#(32)) rg2 <- mkReg(0);

   rule r2;
      rg2 <= x;
   endrule

endmodule

