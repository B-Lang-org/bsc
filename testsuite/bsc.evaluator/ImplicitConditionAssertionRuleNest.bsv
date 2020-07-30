import FIFO::*;

(* synthesize *)
module mkImplicitConditionAssertionRuleNest ();
   Reg#(Bool) b1 <- mkRegU;
   Reg#(Bool) b2 <- mkRegU;
   FIFO#(Bool) f <- mkFIFO;
   rule this_does (b1);
      (* no_implicit_conditions *)
      rule something (b2);
	 f.enq(True);
      endrule
   endrule
endmodule

