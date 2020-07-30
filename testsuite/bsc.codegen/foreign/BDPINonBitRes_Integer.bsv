import "BDPI" function Integer my_func (Bool x);

(* synthesize *)
module mkBDPINonBitRes_Integer ();
   rule r;
      Bit#(32) n = fromInteger (my_func(True));
      $display("%b",n);
      $finish(0);
   endrule
endmodule
