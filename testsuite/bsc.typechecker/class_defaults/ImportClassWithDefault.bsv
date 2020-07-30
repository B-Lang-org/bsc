
import ClassWithDefault::*;

// warn about missing "i" but not "g"
instance C#(UInt#(8));
  function f(x) = x > 17;
  function h(x) = x > 2;
endinstance

UInt#(8) v = 5;

// should use the proper definition of "g"
(* synthesize *)
module sysImportClassWithDefault();
  rule r;
    if (g(v)) $display("1yes"); else $display("1no");
    if (f(v)) $display("2yes"); else $display("2no");
  endrule
endmodule

