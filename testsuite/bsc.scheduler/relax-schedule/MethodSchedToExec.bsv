
(* synthesize *)
module mkTest();
   SubIfc i <- mkSub;

   rule top_rule;
      i.meth1();
   endrule
endmodule

interface SubIfc;
   method Action meth1();
endinterface

(* synthesize *)
module mkSub(SubIfc);

   Reg#(int) rg1 <- mkRegU;
   Reg#(Bool) rg2 <- mkRegU;
   Reg#(Bool) rg3 <- mkRegU;

   rule rule1;
      // (1) conflict with meth1 (via rg1)
      // (2) SB rule2 (via rg3)
      rg1 <= rg1 + (rg3 ? 1 : 3);
   endrule

   rule rule2;
      // (1) SA rule1 (via rg3)
      // (2) SB meth1 (via rg2)
      rg3 <= rg2;
   endrule

   method Action meth1();
      // (1) conflict with rule1 (via rg1)
      // (2) SA rule2 (via rg2)
      rg1 <= rg1 + 2;
      rg2 <= True;
   endmethod
endmodule

