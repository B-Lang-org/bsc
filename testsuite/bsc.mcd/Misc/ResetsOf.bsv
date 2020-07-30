import List::*;

(* synthesize *)
module sysResetsOf(Reset r1, Reset r2, Empty ifc);

Reg#(Bit#(8)) r();
mkReg#(0) the_r(r, reset_by(r1));

Reg#(Bit#(8)) s();
mkReg#(0) the_s(s, reset_by(r2));

List#(Reset) resets = resetsOf(r + s);

rule test;
  if (elem(r1,resets) && elem(r2,resets) && !(elem(noReset,resets)))
    $display("PASS");
  else
    $display("FAIL");
  $finish(0);
endrule

endmodule
