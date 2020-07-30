(* synthesize *)
module sysPreemptsSingleton ();
   Reg#(Bool) c1 <- mkReg(True);
   Reg#(Bool) c2 <- mkReg(False);

   Reg#(Bit#(8)) rg <- mkReg(0);

   (* preempts = "r1" *)
   rule r1 (c1);
      rg <= rg + 1;
      c1 <= False;
      c2 <= True;
   endrule

   rule r2 (c2);
      rg <= rg - 1;
      c1 <= True;
      c2 <= False;
   endrule
endmodule

