// For Verilog:
// We expect the rules to schedule with methods first,
// in interface definition order, then with user rules
// in the order they are elaborated (m2, m1, m3, done).
//
// For Bluesim:
// We expct the methods to be ordered by the order of
// actions in the calling rule (m3, m2, m1, done).

import Clocks::*;

interface Ifc;
   method Action m2();
   method Action m1();
   method Action m3();
endinterface

(* synthesize *)
module sysMethodOrder2();
   Ifc sub <- mkSub();

   rule foo;
      sub.m3();
      sub.m2();
      sub.m1();
   endrule

endmodule

(* synthesize *)
module mkSub(Ifc);
   Reg#(Bool) rg1 <- mkReg(True);
   Reg#(Bool) rg2 <- mkReg(True);
   Reg#(Bool) rg3 <- mkReg(True);

   ReadOnly#(Bool) in_reset <- isResetAssertedDirect();

   rule done if (!in_reset);
      $display("Exiting...");
      $finish(0);
   endrule

   method Action m3();
     rg3 <= !rg3;
     $display("Changing r3");
   endmethod

   method Action m1();
     rg1 <= !rg1;
     $display("Changing r1");
   endmethod

   method Action m2();
     rg2 <= !rg2;
     $display("Changing r2");
   endmethod
endmodule
