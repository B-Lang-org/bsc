interface ModIfc;
  method Action foo();
  method Action bar();
endinterface

(* synthesize *)
module sysParamAttribute
          #((* parameter="BOOL_IN" *) parameter Bool bin)
          (Clock clk2, ModIfc ifc);

  Reg#(Bool) r1 <- mkReg(False);
  Reg#(Bool) r2 <- mkReg(True, clocked_by clk2, reset_by noReset);

  method Action foo();
    $display("Foo: %b %b", r1, bin);
  endmethod

  method Action bar();
    $display("Bar: %b", r2);
  endmethod

endmodule