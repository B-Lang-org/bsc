interface ModIfc;
  method Action foo();
  method Action bar();
endinterface

(* synthesize *)
module sysWrongArgType2 #((* port="INC" *) parameter UInt#(4) n)
                        (Clock clk2, ModIfc ifc);

  Reg#(UInt#(4)) r1 <- mkReg(0);
  Reg#(UInt#(4)) r2 <- mkReg(1, clocked_by clk2, reset_by noReset);

  method Action foo();
    $display("Foo: %h", r1);
    r1 <= r1 + n;
  endmethod

  method Action bar();
    $display("Bar: %h", r2);
    r2 <= r2 + n;
  endmethod

endmodule