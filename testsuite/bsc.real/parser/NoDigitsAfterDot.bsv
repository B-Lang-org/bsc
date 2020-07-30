import Real::*;

(* synthesize *)
module sysNoDigitsAfterDot();
    real x = 0.;

    rule r;
      $display(realToString(x));
    endrule
endmodule