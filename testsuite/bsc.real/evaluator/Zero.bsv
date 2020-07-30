import Real::*;

(* synthesize *)
module sysZero();
   function m(s) = $display(message(s,s));

   rule rl_disp;
      match { .ps, .pm, .pe } = decodeReal(0.0);
      m(" 0.0 = (" +
         (ps ? "+" : "-") + ", " +
         integerToString(pm) + ", " +
         integerToString(pe) + ")");

      match { .ns, .nm, .ne } = decodeReal(-0.0);
      m("-0.0 = (" +
         (ns ? "+" : "-") + ", " +
         integerToString(nm) + ", " +
         integerToString(ne) + ")");
   endrule
endmodule
