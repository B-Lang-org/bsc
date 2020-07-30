interface ModIfc;
  method Bool foo(UInt#(4) x);
endinterface

(* synthesize, no_default_clock, always_ready = "foo" *)
module sysNoDefaultClock(ModIfc ifc);

  method Bool foo(UInt#(4) x);
    return (x != 0);
  endmethod

endmodule
