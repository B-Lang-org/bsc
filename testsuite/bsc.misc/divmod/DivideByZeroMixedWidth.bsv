// Divide-by-zero where the two operands have different widths.
//
// The quotient is typed to the dividend and the remainder to the
// divisor, so the two results can have different widths.  Each must be
// all ones at its own width, not at the other operand's width and not
// at the width the division was computed in.
//
// This is the point where the divide-by-zero rule and the mixed-width
// promotion interact: a narrow operand is promoted and the division runs
// at the wider width, so the all-ones result has to survive being
// truncated back down.
//
// Bluesim only: the Verilog backend produces x for all of these.

module sysDivideByZeroMixedWidth();

Reg#(Bit#(64))  a1 <- mkReg(1234567890123456789);
Reg#(Bit#(8))   z1 <- mkReg(0);

Reg#(Bit#(100)) a2 <- mkReg(633825300114114700748351615033);
Reg#(Bit#(32))  z2 <- mkReg(0);

Reg#(Bit#(32))  a3 <- mkReg(4000000000);
Reg#(Bit#(100)) z3 <- mkReg(0);

Reg#(Bit#(128)) a4 <- mkReg(170141183460469231731687303715884105727);
Reg#(Bit#(100)) z4 <- mkReg(0);

Reg#(Bit#(100)) a5 <- mkReg(633825300114114700748351615033);
Reg#(Bit#(128)) z5 <- mkReg(0);

Reg#(Bool) done <- mkReg(False);

rule test (!done);
  $display("64/8    q=%h r=%h", primQuot(a1, z1), primRem(a1, z1));
  $display("100/32  q=%h r=%h", primQuot(a2, z2), primRem(a2, z2));
  $display("32/100  q=%h r=%h", primQuot(a3, z3), primRem(a3, z3));
  $display("128/100 q=%h r=%h", primQuot(a4, z4), primRem(a4, z4));
  $display("100/128 q=%h r=%h", primQuot(a5, z5), primRem(a5, z5));
  done <= True;
endrule

rule quit (done);
  $finish(0);
endrule

endmodule
