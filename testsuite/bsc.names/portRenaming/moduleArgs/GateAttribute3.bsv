interface ModIfc;
  method Action foo();
endinterface

(* synthesize, gate_all_clocks *)
module sysGateAttribute3((* gate_unused *) Clock clk2, ModIfc ifc);

  Reg#(Bool) r1 <- mkReg(False);

  method Action foo();
    $display("Foo: %b", r1);
  endmethod

endmodule