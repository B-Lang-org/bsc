import Real::*;

(* synthesize *)
module sysAddNegInfPosInf();
    Real pos_inf = 2e10000;
    Real neg_inf = -2e10000;

    real x = neg_inf + pos_inf;

    rule r;
      $display("-INF + +INF = " + realToString(x));
    endrule
endmodule
