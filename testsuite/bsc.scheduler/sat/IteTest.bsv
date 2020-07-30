
typedef 6 Width;

typedef  Bit#(Width) Data_t;

//


(*synthesize*)
module sysIteTest();
   Reg#(Data_t) ua <- mkReg(0);
   Reg#(Data_t) ub <- mkReg(0);
   Reg#(Data_t) uc <- mkReg(0);
   Reg#(Data_t) ud <- mkReg(0);

   Reg#(Bool)  ba <- mkReg(False);

   // predicates for aa and ab are disjoint
   rule aa ( (ba ? ua : ub) == 17);
      uc <= uc + 1;
   endrule


   Data_t xx = signExtend(pack(ba));
   rule ab (((xx & ua) | ((~xx) & ub)) != 17);
      uc <= uc + 2;
   endrule

   //  expect warning that bb can never fire
   rule  bb (ua != 0 );
      uc <= uc + 3;
   endrule

endmodule
