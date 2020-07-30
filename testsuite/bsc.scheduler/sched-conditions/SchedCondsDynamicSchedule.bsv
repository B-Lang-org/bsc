import FIFO::*;

interface SubIfc;
   method Action m1();
   method Action m2();
endinterface

// separately synthesize a submodule with a rule between
(* synthesize *)
module mkSchedCondsDynamicSchedule_Sub(SubIfc);
   Reg#(UInt#(8)) rg1 <- mkRegU;
   Reg#(UInt#(8)) rg2 <- mkRegU;
   Reg#(UInt#(8)) rg3 <- mkRegU;

   rule r;
      rg2 <= rg1;
   endrule

   method Action m1();
      rg3 <= rg2;
   endmethod

   method Action m2();
      rg1 <= 0;
   endmethod
endmodule

(* synthesize *)
module sysSchedCondsDynamicSchedule();
   // Require order r1 > r2 via a register
   // which will conflict with order r2 > r1 via the submodule

   SubIfc s <- mkSchedCondsDynamicSchedule_Sub;

   Reg#(UInt#(8)) rg1 <- mkRegU;
   Reg#(UInt#(8)) rg2 <- mkRegU;

   Reg#(Bool) c <- mkRegU;

   rule r1;
      rg2 <= rg1;
      if (c)
         s.m2;
   endrule

   rule r2;
      rg1 <= 0;
      if (!c)
         s.m1;
   endrule
endmodule

