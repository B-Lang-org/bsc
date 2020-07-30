interface ModIfc;
  method Action foo();
endinterface

(* synthesize *)
module sysEmptyParamName#((* parameter="" *) parameter Bool bin) (ModIfc);

  Reg#(Bool) r1 <- mkReg(False);

  method Action foo();
    $display("Foo: %b %b", r1, bin);
  endmethod

endmodule