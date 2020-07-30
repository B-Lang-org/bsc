import Real::*;

(* synthesize *)
module sysSubPosInf();
    Real pos_inf = 2e10000;

    real x = pos_inf - pos_inf;

    rule r;
      $display("+INF - +INF = " + realToString(x));
    endrule
endmodule
