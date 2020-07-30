import Real::*;

(* synthesize *)
module sysSubNegInf();
    Real neg_inf = -2e10000;

    real x = neg_inf - neg_inf;

    rule r;
      $display("-INF - -INF = " + realToString(x));
    endrule
endmodule
