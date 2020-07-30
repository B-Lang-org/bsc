typedef 36 Width;

typedef  Int#(Width) Data_t;


//  a < b == !(b <= a) && a != b


(*synthesize*)
module sysLessThanSTest();
   Reg#(Data_t) ua <- mkReg(0);
   Reg#(Data_t) ub <- mkReg(0);
   Reg#(Data_t) uc <- mkReg(0);

   // predicates for aa and ab are disjoint

   rule aa (ua < ub);
      uc <= uc + 1;
   endrule

   rule ab (ua == ub || (ub <= ua));
      uc <= uc + 2;
   endrule

   //  expect warning that bb can never fire
   rule  bb (ua != 0 );
      uc <= uc + 3;
   endrule

endmodule
