import Real::*;

(* synthesize *)
module sysRoundInfinite();
    Real inf = 2e10000;

    Integer w = round(inf);
    Integer x = ceil(inf);
    Integer y = floor(inf);
    Integer z = trunc(inf);

    function m(s) = $display(message(s,s));

    rule r;
      m("w = " + integerToString(w));
      m("x = " + integerToString(x));
      m("y = " + integerToString(y));
      m("z = " + integerToString(z));
    endrule
endmodule