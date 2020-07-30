interface ModIfc;
  method Action foo();
  method Action bar();
endinterface

(* synthesize
 , gate_prefix = "GATE"
 , gate_all_clocks
 *)
module sysGatePrefix1(Clock clk2, ModIfc ifc);

  Reg#(Bool) r1 <- mkReg(False);
  Reg#(Bool) r2 <- mkReg(True, clocked_by clk2, reset_by noReset);

  method Action foo();
    $display("Foo: %b", r1);
  endmethod

  method Action bar();
    $display("Bar: %b", r2);
  endmethod

endmodule