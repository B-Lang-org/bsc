
(* synthesize *)
module sysMethodConds_RegWrite();
   Reg#(Bit#(16)) rg <- mkReg(0);

   Reg#(Bool) c1 <- mkReg(True);
   Reg#(Bool) c2 <- mkReg(True);

   rule r;
      if (c1)
         rg <= 0;
      else if (c2)
         rg <= 17;
   endrule
endmodule

