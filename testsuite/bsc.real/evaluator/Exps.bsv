(* synthesize *)
module sysExps();
    Real e = exp_e(1);
    Real x = 2 ** 7;
    Real y = 3 ** 2;
    Real z = 10 ** 2;

    function m(s) = $display(message(s,s));

    rule r;
      m("e = " + realToString(e));
      m("pow(2,7) = " + realToString(x));
      m("pow(3,2) = " + realToString(y));
      m("pow(10,2) = " + realToString(z));
    endrule
endmodule