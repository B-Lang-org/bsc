import Real::*;

(* synthesize *)
module sysSqrt();
    real x = sqrt(0.0);
    real y = sqrt(4.0);
    real z = sqrt(10.0);

    function m(s) = $display(message(s,s));

    rule r;
      m("sqrt(0.0) = " + realToString(x));
      m("sqrt(4.0) = " + realToString(y));
      m("sqrt(10.0) = " + realToString(z));
    endrule
endmodule