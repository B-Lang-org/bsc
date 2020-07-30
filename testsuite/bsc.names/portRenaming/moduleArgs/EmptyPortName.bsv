interface ModIfc;
  method Action foo();
endinterface

(* synthesize *)
module sysEmptyPortName((* port="" *) Bool bin, ModIfc ifc);

  Reg#(Bool) r1 <- mkReg(False);

  method Action foo();
    $display("Foo: %b %b", r1, bin);
  endmethod

endmodule