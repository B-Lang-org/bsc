(* synthesize *)
module sysLogs();
    real u = log(1);
    real x = 128.0;
    real y = log2(x);
    real z = 100.0;
    real v = log10(z);
    real w = logb(3,9.0);

    function m(s) = $display(message(s,s));

    rule r;
      m("log(1) = " + realToString(u));
      m("128.0 = " + realToString(x));
      m("log2(128.0) = " + realToString(y));
      m("100.0 = " + realToString(z));
      m("log10(100.0) = " + realToString(v));
      m("logb(3,9.0) = " + realToString(w));
    endrule
endmodule