
// Test when an array selection generates an implicit condition
// (that is exclusive)

// (Eventually this can be represented by a case statement, so it will
// test for case statements in the solvers.)

// we need a submodule with two methods that have exclusive implicit conds
interface Ifc;
   method Action m1();
   method Action m2();
endinterface

module mkArraySelectImplCondTest_Sub(Ifc);
   Reg#(Bool) rg1 <- mkReg(True);
   Reg#(Bool) rg2 <- mkReg(True);

   Reg#(Bool) c <- mkReg(True);

   method Action m1() if (c);
      rg1 <= !rg1;
   endmethod

   // independent action, exclusive condition
   method Action m2() if (!c);
      rg2 <= !rg2;
   endmethod
endmodule

// Aggressive conditions is needed, to get a case statement
(* synthesize *)
(* options = "-aggressive-conditions" *)
module sysArraySelectImplCondTest();
   Ifc ss[4];
   for (Integer i = 0; i < 4; i = i + 1) begin
      ss[i] <- mkArraySelectImplCondTest_Sub;
   end

   // register to make the selection dynamic
   Reg#(Bit#(2)) idx <- mkReg(0);

   // register to make the rule Actions conflict
   Reg#(UInt#(12)) uc <- mkReg(0);

   // the implicit conditions for aa and ab will be disjoint

   rule aa;
      ss[idx].m1();
      uc <= uc + 1;
   endrule

   rule ab;
      ss[idx].m2();
      uc <= uc + 2;
   endrule

   //  expect warning that bb can never fire
   rule  bb (idx == 0);
      uc <= uc + 3;
   endrule

endmodule
