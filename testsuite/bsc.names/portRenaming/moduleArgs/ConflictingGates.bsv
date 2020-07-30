interface ModIfc;
  method Action foo();
  method Action bar();
endinterface

// This should be an error because clk2 is listed as both gated and ungated
(* synthesize, gate_input_clocks="clk2" *)
module sysConflictingGates((* gate_inhigh *) Clock clk2, ModIfc ifc);

  Reg#(Bool) r1 <- mkReg(False, clocked_by clk2, reset_by noReset);
  Reg#(Bool) r2 <- mkReg(True, clocked_by clk2, reset_by noReset);

  method Action foo();
    $display("Foo: %b", r1);
  endmethod

  method Action bar();
    $display("Bar: %b", r2);
  endmethod

endmodule