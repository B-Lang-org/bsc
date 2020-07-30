import Real::*;

(* synthesize *)
module sysMulPosZeroPosInf();
    Real pos_inf = 2e10000;
    Real pos_zero = 0;

    real x = pos_zero * pos_inf;

    rule r;
      $display("+0 * +INF = " + realToString(x));
    endrule
endmodule
