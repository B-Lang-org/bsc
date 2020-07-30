(* synthesize *)
module sysEOSingleton ();
   Reg#(Bool) c <- mkReg(True);
   Reg#(Bit#(8)) rg <- mkReg(0);

   (* execution_order = "r1" *)
   rule r1 (c);
      rg <= 1;
   endrule

   rule r2;
      rg <= 2;
   endrule
endmodule

