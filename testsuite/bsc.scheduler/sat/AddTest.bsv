typedef 36 Width;

typedef  Int#(Width) Data_t;


//  a - b ==  1 + ua + (~bb)


(*synthesize*)
module sysAddTest();
   Reg#(Data_t) ua <- mkReg(0);
   Reg#(Data_t) ub <- mkReg(0);
   Reg#(Data_t) uc <- mkReg(0);

   // predicates for aa and ab are disjoint

   rule aa ((ua - ub)  == 17);
      uc <= uc + 1;
   endrule

   rule ab ((1+ ua + (unpack(~pack(ub)))) != 17 );
      uc <= uc + 2;
   endrule

   //  expect warning that bb can never fire
   rule  bb (ua != 0 );
      uc <= uc + 3;
   endrule

endmodule
