import "BDPI" function ActionValue#(Bit#(128)) my_wide_time ();

(* synthesize *)
module mkBDPIActionValueIgnoreWideReturn ();
   rule r;
      let a <- my_wide_time();
      $finish(0);
   endrule
endmodule
