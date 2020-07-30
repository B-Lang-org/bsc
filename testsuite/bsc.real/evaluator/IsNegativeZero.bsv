import Real::*;

(* synthesize *)
module sysIsNegativeZero();

    Real x = -0.0;
    Real y = 0.0;

    function m(s) = $display(message(s,s));

    rule r;
      if (isNegativeZero(x))
         m("-0.0: " + realToString(x));
      else
         m("ERROR: " + realToString(x));
      if (isNegativeZero(y))
         m("ERROR: " + realToString(y));
      else
         m("0.0: " + realToString(y));
    endrule
endmodule