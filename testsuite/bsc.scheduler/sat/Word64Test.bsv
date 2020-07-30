
// Test constants of width 33 to 64
// (Here, we test width 33, using all 1's, to see if the msb is truncated)

(*synthesize*)
module sysWord64Test();
   Reg#(Bit#(64)) ua <- mkReg(0);
   Reg#(Bit#(64)) ub <- mkReg(0);
   Reg#(Bit#(64)) uc <- mkReg(0);

   // predicates for aa and ab are disjoint

   rule aa (ua[63:31] == 33'h1FFFFFFFF);
      uc <= uc + 1;
   endrule

   rule ab (ua[63:31] == 33'h0FFFFFFFF);
      uc <= uc + 2;
   endrule

   //  expect warning that bb can never fire
   rule  bb ((ua[63:62] == 2'b11) && (ua[61:31] == 31'h7FFFFFFF));
      uc <= uc + 3;
   endrule

endmodule
