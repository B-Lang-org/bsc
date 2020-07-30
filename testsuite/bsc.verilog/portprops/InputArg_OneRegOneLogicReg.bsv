(* synthesize *)
module sysInputArg_OneReg #(Bit#(16) b) ();
   Reg#(Bit#(16)) rg1 <- mkReg(0);
   Reg#(Bit#(16)) rg2 <- mkReg(0);

   rule r;
      rg1 <= b;
      rg2 <= b + 1;
   endrule
endmodule

