import "BDPI" function String my_itos (Bit#(8) x);

(* synthesize *)
module mkBDPIStringResult ();
   rule r;
      $display("%s",my_itos(37));
      $finish(0);
   endrule
endmodule
