import List::*;

(* synthesize *)
module sysClocksOf#(Clock c, Clock c2)(Empty);

Reg#(Bit#(8)) r();
mkRegU the_r(r, clocked_by(c));

Reg#(Bit#(8)) s();
mkRegU the_s(s, clocked_by(c2));

List#(Clock) clocks = clocksOf(r + s);

rule test;
  if (elem(c,clocks) && elem(c2,clocks) && !(elem(noClock,clocks)))
    $display("PASS");
  else
    $display("FAIL");
  $finish(0);
endrule

endmodule
