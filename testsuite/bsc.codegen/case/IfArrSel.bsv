(* synthesize *)
module sysIfArrSel();
   Reg#(Bit#(3)) rg <- mkReg(0);
   Reg#(Bit#(8)) rg2 <- mkRegU;
   Bit#(8) ns[3] = { 17, 42, 2 };
   rule r;
      Bit#(8) n;
      if (rg == 3)
         n = 22;
      else if (rg == 4)
         n = 23;
      else if ((rg == 5) || (rg == 6) || (rg == 7))
         n = 5;
      else
         n = ns[rg];
      rg2 <= n;
   endrule
endmodule
