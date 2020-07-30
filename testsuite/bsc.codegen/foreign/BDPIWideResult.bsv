import "BDPI" function Bit#(128) four_copies(Bit#(32) x);

(* synthesize *)
module mkBDPIWideResult ();
   rule r;
      $display("%h", four_copies(32'hdeadbeef));
      $finish(0);
   endrule
endmodule
