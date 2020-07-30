import Real::*;

(* synthesize *)
module sysIsInfinite();

    Real x = 2e10000;

    function m(s) = $display(message(s,s));

    rule r;
      if (isInfinite(x))
         m("isInfinite: " + realToString(x));
      else
         m("ERROR: " + realToString(x));
    endrule
endmodule