// When a priority mux is constructed, two rules which share the same value
// have to be separated into different arms if their priority is different.

(* synthesize *)
module sysPriMux_SharedValue ();

   // use registers to enforce an earliness order
   Reg#(Bool) b1 <- mkReg(False);
   Reg#(Bool) b2 <- mkReg(False);
   Reg#(Bool) b3 <- mkReg(False);

   // the register with the PriMux input
   Reg#(Bit#(2)) r <- mkReg(0);

   // Three rules, executing in order A, B, C,
   // where rules A and C use the same value but not different from B.

   rule rA (b1);
      r <= 1;
      b2 <= True;
   endrule
      
   rule rB (b2);
      r <= 2;
      b3 <= True;
   endrule
      
   rule rC (b3);
      r <= 1;
   endrule

endmodule

