typedef 36 Width;

typedef  Bit#(Width) Data_t;


// a[7;5] == tuncate (a >> 5)


(*synthesize*)
module sysAddTest();

   Reg#(Data_t) ua <- mkReg(0);
   
   Reg#(Data_t) uc <- mkReg(0);

   
   // predicates for aa and ab are disjoint

   rule aa (ua[17:5] == 17 );
      uc <= uc + 1;
   endrule
   
   Bit#(15) d = truncate (ua >> 3);
   //d = ua[17:5];
   rule ab ((d >> 2) != 17);
      uc <= uc + 2;
   endrule

   //  expect warning that bb can never fire
   rule  bb (ua != 0 );
      uc <= uc + 3;
   endrule

endmodule
