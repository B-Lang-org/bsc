(* synthesize *)
module sysFractionalLeadingZeros();
    real x = 1.02;
    real y = 1.002;
    real z = 1.00000000002;

    function m(s) = $display(message(s,s));

    rule r;
      m("1.02 = " + realToString(x));
      m("1.002 = " + realToString(y));
      m("1.00000000002 = " + realToString(z));
    endrule
endmodule