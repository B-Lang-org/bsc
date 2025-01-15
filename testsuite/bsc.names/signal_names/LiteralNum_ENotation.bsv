// ---------------------------------------------------------------------------

import Real::*;

(* synthesize *)
module sysLiteralNum_ENotation ();

  Reg#(Bool) rg_start <- mkReg(True);

  rule do_disp (rg_start);
    rg_start <= False;
    for (Integer i=0; i<4; i=i+1) begin
      Real r = (pi * (2**fromInteger(i))) / (2**10);
      $display("%d: %f", i, r);
    end
    $finish(0);
  endrule

endmodule

// ---------------------------------------------------------------------------
