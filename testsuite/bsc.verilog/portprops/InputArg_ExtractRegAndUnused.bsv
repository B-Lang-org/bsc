(* synthesize *)
module sysInputArg_ExtractRegAndUnused #(Bit#(16) b) ();
   Reg#(Bit#(8)) rg <- mkReg(0);

   rule r;
      rg <= truncate(b);
   endrule
endmodule

