import "BDPI" function Bit#(32) my_stoi (String x);

(* synthesize *)
module mkBDPIStringArg ();
   rule r;
      $display("%d",my_stoi("0x17"));
      $finish(0);
   endrule
endmodule
