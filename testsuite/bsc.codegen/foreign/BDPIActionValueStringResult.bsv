import "BDPI" function ActionValue#(String) my_itos (Bit#(8) x);

(* synthesize *)
module mkBDPIStringResult ();
   rule r;
      String s <- my_itos(37);
      $display("%s", s);
      $finish(0);
   endrule
endmodule
