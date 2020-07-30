interface ModIfc;
  method Action foo();
endinterface

(* synthesize
 , default_reset = "RESET"
 *)
module sysDefaultReset(ModIfc ifc);

  Reg#(Bool) r1 <- mkReg(False);

  method Action foo();
    $display("Foo: %b", r1);
  endmethod

endmodule