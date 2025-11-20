

(* synthesize *)
module sysLargeReal();
    Real inf = 2e1_000_000_000_000;
    Real zero = 2e-1_000_000_000_000;

    // just under the limit
    Real inf2 = 2e999_99;
    Real zero2 = 2e-999_99;

    function m(s) = $display(message(s,s));

    rule r;
      m("inf = " + realToString(inf));
      m("zero = " + realToString(zero));
      m("inf2 = " + realToString(inf2));
      m("zero2 = " + realToString(zero2));
    endrule
endmodule