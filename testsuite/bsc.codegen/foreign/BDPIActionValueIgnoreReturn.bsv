import "BDPI" function ActionValue#(Bit#(32)) my_time (Bit#(8) x);

(* synthesize *)
module mkBDPIActionValueIgnoreReturn ();
   rule r;
      let a <- my_time(0);
      $finish(0);
   endrule
endmodule
