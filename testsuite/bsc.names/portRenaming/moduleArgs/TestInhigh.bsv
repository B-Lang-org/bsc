import Clocks::*;

(* synthesize, gate_all_clocks *)
module sysTestInhigh();

  Clock clk2 <- mkAbsoluteClock(18,7);

  Empty sub <- mkSub(clk2);

endmodule

(* synthesize, default_gate_inhigh *)
module mkSub(Clock clk2, Empty ifc);

  Reg#(Bool) r1 <- mkReg(False, clocked_by clk2, reset_by noReset);

  rule print;
    $display(r1);
    r1 <= !r1;
  endrule

endmodule