(* synthesize *)
module sysSizeZeroIndex();
   Reg#(Bit#(0)) rg <- mkRegU;
   Reg#(Bit#(8)) rg2 <- mkRegU;
   Bit#(8) ns[2] = { 17, 42 };
   rule r;
      rg2 <= ns[rg];
   endrule
endmodule
