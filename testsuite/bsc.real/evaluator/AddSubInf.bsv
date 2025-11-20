

(* synthesize *)
module sysAddSubInf();
    Real pos_inf = 2e10000;
    Real neg_inf = -2e10000;

    real w = pos_inf + pos_inf;
    real x = neg_inf + neg_inf;
    real y = pos_inf - neg_inf;
    real z = neg_inf - pos_inf;

    function m(s) = $display(message(s,s));

    rule r;
      m("+INF + +INF = " + realToString(w));
      m("-INF + -INF = " + realToString(x));
      m("+INF - -INF = " + realToString(y));
      m("-INF - +INF = " + realToString(z));
    endrule
endmodule
