(* synthesize *)
module sysSizeZeroElems();
   Reg#(Bit#(2)) rg <- mkRegU;
   Bit#(0) ns[4] = { 0, 0, 0, 0 };
   rule r;
      $display(ns[rg]);
   endrule
endmodule
