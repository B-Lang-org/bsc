import "BDPI" function Bit#(m) bit_dup (Bit#(n) x, Bit#(32) nsz)
   provisos(Add#(n, n, m));

(* synthesize *)
module mkBDPICtxViolated();
   rule r;
      Bit#(15) y = bit_dup(8'h5A, 8);
      $display("%h", y);
   endrule
endmodule
