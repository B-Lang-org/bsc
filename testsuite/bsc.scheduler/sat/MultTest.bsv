// XXX STP slows down when this is 16 or higher
typedef 12 Width;

typedef  Int#(Width) Data_t;

//  a * b * 11 ==  a * (b + 2b + 8b)

(*synthesize*)
module sysMultTest();
   Reg#(Data_t) ua <- mkReg(0);
   Reg#(Data_t) ub <- mkReg(0);
   Reg#(Data_t) uc <- mkReg(0);

   // predicates for aa and ab are disjoint

   rule aa ((11 * ua * ub) == 17);
      uc <= uc + 1;
   endrule
   
   let ub11 = ub + (ub << 1) + (ub << 3);
   rule ab (ub11 * ua != 17 );
      uc <= uc + 2;
   endrule

   //  expect warning that bb can never fire
   rule  bb (ua != 0 );
      uc <= uc + 3;
   endrule

endmodule
