
module sysDivideByZeroStatic();

Reg#(UInt#(96)) a <- mkReg(1203 / 0);
Reg#(UInt#(96)) b <- mkReg(1203 * 0);

Reg#(Bool) done <- mkReg(False);

rule test (!done);
  $display(a, b);
  done <= True;
endrule

rule quit (done);
  $finish(0);
endrule

endmodule
