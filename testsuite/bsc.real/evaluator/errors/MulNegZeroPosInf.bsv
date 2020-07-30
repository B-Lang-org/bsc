import Real::*;

(* synthesize *)
module sysMulNegZeroPosInf();
    Real pos_inf = -2e10000;
    Real neg_zero = -0.0;

    real x = neg_zero * pos_inf;

    rule r;
      $display("-0 * +INF = " + realToString(x));
    endrule
endmodule
