import "BDPI" function Action my_display (Bit#(8) x);

(* synthesize *)
module mkBDPIAction ();
   rule r;
      my_display(45);
      $finish(0);
   endrule
endmodule
