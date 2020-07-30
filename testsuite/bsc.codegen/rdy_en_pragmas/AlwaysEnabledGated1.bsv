import Clocks::*;

interface Test;
  method Action inc;
  method Bit#(32) count;
  interface Clock gated_clk;
endinterface

(* always_enabled *)
(* synthesize *)
module mkTestGated1(Test);

  Reg#(Bool) rdy <- mkReg(True);

  GatedClockIfc gc <- mkGatedClockFromCC(True);

  rule drive_gate;
    gc.setGateCond(rdy);
  endrule

  Reg#(Bit#(32)) countReg <- mkRegA(0, clocked_by gc.new_clk);
  
  rule flip;
    rdy <= !rdy;
  endrule

  method Action inc;
    countReg <= countReg + 1;
  endmethod

  method count = countReg;

  interface gated_clk = gc.new_clk;

endmodule

(* synthesize *)
module sysAlwaysEnabledGated1();

  Reg#(Bit#(32)) cycle <- mkReg(0);

  Test dut <- mkTestGated1;

  rule inc;
    dut.inc;
  endrule

  (* no_implicit_conditions *)
  (* fire_when_enabled *)
  rule test;
    $display("Cycle: %0d, Count: %0d", cycle, dut.count);
    if(cycle == 20) $finish(0);
    cycle <= cycle + 1;
  endrule

endmodule


