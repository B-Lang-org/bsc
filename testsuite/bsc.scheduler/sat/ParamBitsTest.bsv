
// Test bit-vectore module parameter

(*synthesize*)
module sysParamBitsTest#(parameter Bit#(8) p)();
   Reg#(UInt#(12)) uc <- mkReg(0);

   // predicates for aa and ab are disjoint

   rule aa (p == 17);
      uc <= uc + 1;
   endrule

   rule ab (p != 17);
      uc <= uc + 2;
   endrule

   //  expect warning that bb can never fire
   rule bb;
      uc <= uc + 3;
   endrule

endmodule
