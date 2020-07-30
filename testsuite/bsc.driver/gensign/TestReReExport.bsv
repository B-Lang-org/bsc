import BasicReReExport::*;

(* synthesize *)
module sysTestReReExport();

  S x = S { b1: myFn1(0) == 1,
            b2: myFn2(3) == 2 };
  S y = S { b1: myFn1(1) == 1,
            b2: myFn2(4) == 2 };

  Reg#(Bool) done <- mkReg(False);

  rule doDisplay (!done);
    $display("Values = %d, %d, %d, %d", x.b1, x.b2, y.b1, y.b2);
    done <= True;
  endrule

  rule doFinish (done);
    $finish(0);
  endrule

endmodule