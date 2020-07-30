interface ModIfc;
  method Action foo();
  method Action bar();
endinterface

(* synthesize *)
module sysWrongArgType3(Clock clk2, (* reset="RST" *) ModIfc ifc);

  Reg#(Bool) r1 <- mkReg(False);
  Reg#(Bool) r2 <- mkReg(True, clocked_by clk2, reset_by noReset);

  method Action foo();
    $display("Foo: %b", r1);
  endmethod

  method Action bar();
    $display("Bar: %b", r2);
  endmethod

endmodule