(* synthesize *)
module sysCaseArrSel();
   Reg#(Bit#(3)) rg <- mkReg(0);
   Reg#(Bit#(8)) rg2 <- mkRegU;
   Bit#(8) ns[3] = { 17, 42, 2 };
   rule r;
      Bit#(8) n;
      case (rg)
         3 : n = 22;
         4 : n = 23;
         5 : n = 5;
         6 : n = 5;
         7 : n = 5;
         default: n = ns[rg];
      endcase
      rg2 <= n;
   endrule
endmodule
