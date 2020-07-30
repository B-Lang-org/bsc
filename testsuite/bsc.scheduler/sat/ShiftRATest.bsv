typedef 18 Width;

typedef  Int#(Width) Data_t;


//  A >> B == A / D when D = 1 << (B-1)


(*synthesize*)
module sysShiftRATest();
   Reg#(Data_t) ua <- mkReg(0);
   Reg#(Data_t) ub <- mkReg(0);
   Reg#(Data_t) uc <- mkReg(0);

   // predicates for aa and ab are disjoint

   rule aa ((ua >> ub)  == 17);
      uc <= uc + 1;
   endrule

   let d = 1 << (ub);
   rule ab (ua/d != 17);
      uc <= uc + 2;
   endrule

   //  expect warning that bb can never fire
   rule  bb (ua != 0 );
      uc <= uc + 3;
   endrule

endmodule
