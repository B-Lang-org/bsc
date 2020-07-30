import "BDPI" function ActionValue#(Bit#(32)) my_time (Bit#(8) x);

(* synthesize *)
module mkBDPIActionValue ();
   rule r;
      let a <- my_time(0);
      $display("%d",a);
      $finish(0);
   endrule
endmodule
