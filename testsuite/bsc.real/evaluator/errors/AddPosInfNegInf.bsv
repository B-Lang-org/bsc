import Real::*;

(* synthesize *)
module sysAddPosInfNegInf();
    Real pos_inf = 2e10000;
    Real neg_inf = -2e10000;

    real x = pos_inf + neg_inf;

    rule r;
      $display("+INF + -INF = " + realToString(x));
    endrule
endmodule
