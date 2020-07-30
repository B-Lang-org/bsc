

typedef  Bool Data_t;

// Test Boolean operator with DeMorgan's law
// A || B == !B && !A

(*synthesize*)
module sysBoolTest();
   Reg#(Data_t) ua <- mkReg(False);
   Reg#(Data_t) ub <- mkReg(False);
   Reg#(UInt#(12)) uc <- mkReg(0);

   // predicates for aa and ab are disjoint

   rule aa ((ua || ub));
      uc <= uc + 1;
   endrule

   rule ab (!ub && !ua);
      uc <= uc + 2;
   endrule

   //  expect warning that bb can never fire
   rule  bb (ua );
      uc <= uc + 3;
   endrule

endmodule
