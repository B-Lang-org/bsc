interface ModIfc;
  method Action foo();
endinterface

(* synthesize
 , default_clock_osc = "CLOCK"
 , default_clock_gate = "GATE"
 *)
module sysDefaultClock(ModIfc ifc);

  Reg#(Bool) r1 <- mkReg(False);

  method Action foo();
    $display("Foo: %b", r1);
  endmethod

endmodule