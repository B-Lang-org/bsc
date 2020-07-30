import Real::*;
import List::*;

(* synthesize *)
module sysIntrospectInfinite();
    Real pos_inf = (2**100000);
    Real neg_inf = -pos_inf;

    let dpi = decodeReal(pos_inf);
    let dni = decodeReal(neg_inf);

    let spi = splitReal(pos_inf);
    let sni = splitReal(neg_inf);

    match { .ds_pi, .exp_pi } = realToDigits(10, pos_inf);
    match { .ds_ni, .exp_ni } = realToDigits(10, neg_inf);

    function m(s) = $display(message(s,s));

    function dispDigit(d) = m("   " + integerToString(d));

    rule r;
      m("INF = " + realToString(pos_inf));
      m("INF bits = (" +
         (tpl_1(dpi) ? "+" : "-") + ", " +
         integerToString(tpl_2(dpi)) + ", " +
         integerToString(tpl_3(dpi)) + ")");
      m("-INF = " + realToString(neg_inf));
      m("-INF bits = (" +
         (tpl_1(dni) ? "+" : "-") + ", " +
         integerToString(tpl_2(dni)) + ", " +
         integerToString(tpl_3(dni)) + ")");

      m("INF parts = (" +
        integerToString(tpl_1(spi)) + ", " +
        realToString(tpl_2(spi)) + ")");
      m("-INF parts = (" +
        integerToString(tpl_1(sni)) + ", " +
        realToString(tpl_2(sni)) + ")");

      m("INF digits = ");
      joinActions(map(dispDigit, ds_pi));
      m("INF exponent = " + integerToString(exp_pi));
      m("-INF digits = ");
      joinActions(map(dispDigit, ds_ni));
      m("-INF exponent = " + integerToString(exp_ni));
    endrule
endmodule