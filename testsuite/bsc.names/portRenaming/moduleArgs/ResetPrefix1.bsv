interface ModIfc;
  method Action foo();
  method Action bar();
endinterface

(* synthesize
 , reset_prefix = "RESET"
 *)
module sysResetPrefix1(Clock clk2, Reset rst2, ModIfc ifc);

  Reg#(Bool) r1 <- mkReg(False);
  Reg#(Bool) r2 <- mkReg(True, clocked_by clk2, reset_by rst2);

  method Action foo();
    $display("Foo: %b", r1);
  endmethod

  method Action bar();
    $display("Bar: %b", r2);
  endmethod

endmodule
