interface ModIfc;
  method Action foo();
  method Action bar();
  interface Inout#(Bool) out_io;
endinterface

(* synthesize *)
module sysPortAttribute
          #((* parameter="in_io" *) parameter Bool bin)
          (Clock clk2, Inout#(Bool) in_io, ModIfc ifc);

  Reg#(Bool) r1 <- mkReg(False);
  Reg#(Bool) r2 <- mkReg(True, clocked_by clk2, reset_by noReset);

  method Action foo();
    $display("Foo: %b %b", r1, bin);
  endmethod

  method Action bar();
    $display("Bar: %b", r2);
  endmethod

endmodule