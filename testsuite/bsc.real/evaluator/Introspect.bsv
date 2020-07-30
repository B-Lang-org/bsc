import Real::*;
import List::*;

(* synthesize *)
module sysIntrospect();
    Real w = 2;
    let dw = decodeReal(w);
    let dnw = decodeReal(-w);
    let dw2 = decodeReal(w * (2 ** 10));
    let dw3 = decodeReal(w + 0.5);

    Real x = 2.5;
    let sx = splitReal(x);

    Real y = ((10**12) + 10000) / 3;
    match { .ds1, .exp1 } = realToDigits(10, y);
    match { .ds2, .exp2 } = realToDigits(10, -y);

    function m(s) = $display(message(s,s));

    function dispDigit(d) = m("   " + integerToString(d));

    rule r;
      m("w = 2.0 = " + realToString(w));
      m("w bits = (" +
         (tpl_1(dw) ? "+" : "-") + ", " +
         integerToString(tpl_2(dw)) + ", " +
         integerToString(tpl_3(dw)) + ")");
      m("-w bits = (" +
         (tpl_1(dnw) ? "+" : "-") + ", " +
         integerToString(tpl_2(dnw)) + ", " +
         integerToString(tpl_3(dnw)) + ")");
      m("w2 bits = (" +
         (tpl_1(dw2) ? "+" : "-") + ", " +
         integerToString(tpl_2(dw2)) + ", " +
         integerToString(tpl_3(dw2)) + ")");
      m("w3 bits = (" +
         (tpl_1(dw3) ? "+" : "-") + ", " +
         integerToString(tpl_2(dw3)) + ", " +
         integerToString(tpl_3(dw3)) + ")");
      Bit#(53) m3 = 5 << 50;
      m("w3 mantissa should be '" + bitToString(m3) + "'");

      m("x = 2.5 = " + realToString(x));
      m("x parts = (" +
        integerToString(tpl_1(sx)) + ", " +
        realToString(tpl_2(sx)) + ")");

      m("y = " + realToString(y));
      m("y digits: ");
      joinActions(map(dispDigit, ds1));
      m("y exponent: " + integerToString(exp1));

      m("-y = " + realToString(-y));
      m("-y digits: ");
      joinActions(map(dispDigit, ds2));
      m("-y exponent: " + integerToString(exp2));
    endrule
endmodule