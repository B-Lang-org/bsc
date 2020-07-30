
// Test Boolean module parameter

(*synthesize*)
module sysParamBoolTest#(parameter Bool p)();
   Reg#(UInt#(12)) uc <- mkReg(0);

   // predicates for aa and ab are disjoint

   rule aa (p);
      uc <= uc + 1;
   endrule

   rule ab (!p);
      uc <= uc + 2;
   endrule

   //  expect warning that bb can never fire
   rule bb;
      uc <= uc + 3;
   endrule

endmodule
