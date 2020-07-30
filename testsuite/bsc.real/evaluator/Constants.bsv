import Real::*;

(* synthesize *)
module sysConstants();
    // only one constant currently
    Real x = pi;

    function m(s) = $display(message(s,s));

    rule r;
      m("pi = " + realToString(x));
    endrule
endmodule