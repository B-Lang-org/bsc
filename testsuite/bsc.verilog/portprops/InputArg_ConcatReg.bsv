(* synthesize *)
module sysInputArg_ConcatReg #(Bit#(16) b) ();
   Reg#(Bit#(32)) rg <- mkReg(0);

   rule r;
      rg <= {b, 17};
   endrule
endmodule

