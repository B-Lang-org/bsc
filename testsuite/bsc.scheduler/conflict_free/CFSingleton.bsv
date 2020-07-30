(* synthesize *)
module sysCFSingleton ();
   Reg#(Bool) c <- mkReg(True);

   Reg#(Bit#(8)) rg[2];
   rg[0] <- mkReg(0);
   rg[1] <- mkReg(0);

   Reg#(Bit#(1)) idx1 <- mkReg(0);
   Reg#(Bit#(1)) idx2 <- mkReg(1);

   (* conflict_free = "r1" *)
   rule r1 (c);
      rg[idx1] <= rg[idx1] + 1;
      idx1 <= idx1 + 1;
   endrule

   rule r2;
      rg[idx2] <= rg[idx2] + 1;
      idx2 <= idx2 + 1;
   endrule
endmodule

