import Clocks::*;

(* synthesize *)
module sysPreempt();

  Clock clk2 <- mkAbsoluteClock(7,15);
  Reset rst2 <- mkInitialReset(1, clocked_by clk2);

  Reg#(UInt#(8)) val1 <- mkRegA(19);
  Reg#(UInt#(8)) val2 <- mkRegA(46, clocked_by clk2, reset_by rst2);

  Reg#(Bool) cond1 <- mkRegA(False);
  Reg#(Bool) cond2 <- mkRegA(True, clocked_by clk2, reset_by rst2);

  (* preempts = "r1, r2" *)
  rule r1 (cond1);
    $display("Rule1");
  endrule

  rule r2 (!cond2);
    $display("Rule2");
  endrule

endmodule