import Real::*;

(* synthesize *)
module sysMulNegZeroNegInf();
    Real neg_inf = -2e10000;
    Real neg_zero = -0.0;

    real x = neg_zero * neg_inf;

    rule r;
      $display("-0 * -INF = " + realToString(x));
    endrule
endmodule
