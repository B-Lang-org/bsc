(* synthesize *)
module sysInputArg_OneReg #(Bit#(16) b) ();
   Reg#(Bit#(16)) rg <- mkReg(0);

   rule r;
      rg <= b;
   endrule
endmodule

