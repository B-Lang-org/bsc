interface ModIfc;
  method Action foo();
endinterface

(* synthesize, no_default_reset *)
module sysNoDefaultReset(ModIfc ifc);

  Reg#(Bool) r1 <- mkReg(False, reset_by noReset);

  method Action foo();
    $display("Foo: %b", r1);
  endmethod

endmodule