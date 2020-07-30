interface ModIfc;
  method Action foo();
  method Action bar();
endinterface

(* synthesize *)
module sysPortAttribute(Clock clk2, (* port="BOOL_IN" *) Bool bin, ModIfc ifc);

  Reg#(Bool) r1 <- mkReg(False);
  Reg#(Bool) r2 <- mkReg(True, clocked_by clk2, reset_by noReset);

  method Action foo();
    $display("Foo: %b %b", r1, bin);
  endmethod

  method Action bar();
    $display("Bar: %b", r2);
  endmethod

endmodule