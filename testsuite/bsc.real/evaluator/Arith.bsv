(* synthesize *)
module sysArith();
    Real w = 1.2;
    Real x = 1.1;
    Real y = 1.2;
    Real z = 1.3;
    Real v = 1;

    Real v2 = v + x + w;
    Real v3 = v2 - z;

    function m(s) = $display(message(s,s));

    rule r;
      m("1 + 1.1 + 1.2 = " + realToString(v2));
      m("1 + 1.1 + 1.2 - 1.3= " + realToString(v3));
      m("1.1 * 1.3 = " + realToString(x*z));
      m("-1.1 = " + realToString(-x));
      m("5.0 / 2 = " + realToString(5.0 / 2));
      m("abs -1.1 = " + realToString(abs(-x)));
      m("signum -1.1 = " + realToString(signum(-x)));
    endrule
endmodule