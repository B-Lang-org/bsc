import Real::*;

(* synthesize *)
module sysMulPosZeroNegInf();
    Real neg_inf = -2e10000;
    Real pos_zero = 0;

    real x = pos_zero * neg_inf;

    rule r;
      $display("+0 * -INF = " + realToString(x));
    endrule
endmodule
