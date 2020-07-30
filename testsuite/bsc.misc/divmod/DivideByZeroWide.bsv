
module sysDivideByZeroWide();

Reg#(UInt#(96)) a <- mkReg(1203);
Reg#(UInt#(96)) b <- mkReg(0);

Reg#(Bool) done <- mkReg(False);

rule test (!done);
  a <= a / b;
  b <= a % b;
  done <= True;
endrule

rule quit (done);
  $display(a, b);
  $finish(0);
endrule

endmodule
