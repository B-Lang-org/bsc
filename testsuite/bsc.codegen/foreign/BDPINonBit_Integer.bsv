import "BDPI" function Bool my_xor (Integer x, Integer y);

(* synthesize *)
module mkBDPINonBit_Integer ();
   rule r;
      $display("%b",my_xor(0,1));
      $finish(0);
   endrule
endmodule
