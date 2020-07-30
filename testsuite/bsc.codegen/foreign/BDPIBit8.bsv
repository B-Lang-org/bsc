import "BDPI" function Bit#(8) my_and (Bit#(8) x, Bit#(8) y);

import "BDPI" my_C_or = function Bit#(8) my_or (Bit#(8) x, Bit#(8) y);

(* synthesize *)
module mkBDPIBit8 ();
   rule r;
      $display("%d",my_and(1,2));
      $display("%d",my_or(1,2));
      $finish(0);
   endrule
endmodule

