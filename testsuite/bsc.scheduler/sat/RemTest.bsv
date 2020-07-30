typedef  2 Width;

typedef  UInt#(Width) Data_t;





(*synthesize*)
module sysRemTest();
   Reg#(Data_t) ua <- mkReg(0);
   Reg#(Data_t) ub <- mkReg(0);
   Reg#(Data_t) uc <- mkReg(0);



   rule aa (ub!=0 && ((ua % ub)  == 1));
      uc <= uc + 1;
   endrule

   rule ab (ub <= 1);
      uc <= uc + 2;
   endrule

   rule ac (ua == 0 && ub > 1);
      uc <= uc + 2;
   endrule

   rule ad (ua==2 && (ub == 2 || ub ==3));
      uc <= uc + 3;
   endrule

   rule ae (ub !=0 && ua==3 && ub > 2);
      uc <= uc - 2;
   endrule

   //  expect warning that bb can never fire
   rule  bb (ua != 0 );
      uc <= uc + 3;
   endrule

endmodule
