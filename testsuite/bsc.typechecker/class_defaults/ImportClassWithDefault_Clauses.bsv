
import ClassWithDefault_Clauses::*;

// warn about missing "i" but not "g"
instance C#(Bit#(1));
  function f(x) = (x > 17) ? 1 : 0;
  function h(x) = (x > 2) ? 1 : 0;
endinstance

Integer v = 5;

// should use the proper definition of "g"
(* synthesize *)
module sysImportClassWithDefault_Clauses();
  rule r;
    if (g(v)) $display("1yes"); else $display("1no");
    if (f(v)) $display("2yes"); else $display("2no");
  endrule
endmodule

