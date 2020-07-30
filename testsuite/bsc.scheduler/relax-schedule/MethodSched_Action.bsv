interface SubIFC;
   method Action m1();
   method Action m2();
endinterface

(* synthesize *)
module mkMethodSched_Action_Sub (SubIFC);
   Reg#(int) rg <- mkReg(0);
   Reg#(int) rg2 <- mkReg(0);

   // conflicts with m1, but SB m2
   rule sub_rule;
      rg <= rg + 2;
      rg2 <= rg2 + 1;
   endrule

   method Action m1();
      rg <= rg + 1;
   endmethod

   method Action m2();
      rg2 <= 17;
   endmethod
endmodule

(* synthesize *)
module sysMethodSched_Action();
   SubIFC s <- mkMethodSched_Action_Sub;

   Reg#(Bool) q <- mkReg(True);
   Reg#(Bool) p <- mkReg(True);

   rule top_rule;
      q <= True;
      if (p)
	 s.m1();
   endrule

   rule top_rule_2;
      // make SB rule2
      q <= !q;
      s.m2();
   endrule


endmodule
