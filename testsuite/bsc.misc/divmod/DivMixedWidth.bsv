// Division where the two operands have different widths.
//
// BSC does not require the operands of a division to be the same width,
// and the result is typed to just one of them:
//   primQuot :: Bit k -> Bit n -> Bit k   (result = dividend width)
//   primRem  :: Bit k -> Bit n -> Bit n   (result = divisor  width)
// These are reachable from the exported Prelude functions unsignedQuot
// and signedQuot as well as from primQuot/primRem directly.
//
// Bluesim used to get all of the mixed cases wrong:
//   - a wide operand with a narrow one failed to compile at all, both
//     when the result was narrow (no matching C++ operator) and when it
//     was wide (no wop_quot/wop_rem taking a plain integer);
//   - two wide operands with the dividend wider than the divisor hung
//     forever, because wide_quot_rem forms (divisor << shift) and the
//     shift preserves the divisor's width, silently truncating it.
//
// The divisors live in registers so nothing is constant-folded.
//
// Bluesim only: iverilog cannot do wide division (see divmod.exp).

module sysDivMixedWidth();

// narrow / narrow, mismatched widths
Reg#(Bit#(64))  a1 <- mkReg(1234567890123456789);
Reg#(Bit#(8))   b1 <- mkReg(7);

// wide / wide, equal widths
Reg#(Bit#(96))  a2 <- mkReg(39614081257132168796771975173);
Reg#(Bit#(96))  b2 <- mkReg(1099511627779);

// wide / narrow
Reg#(Bit#(100)) a3 <- mkReg(633825300114114700748351615033);
Reg#(Bit#(32))  b3 <- mkReg(1000003);

// narrow / wide
Reg#(Bit#(32))  a4 <- mkReg(4000000000);
Reg#(Bit#(100)) b4 <- mkReg(1180591620717411303431);

// wide / wide, divisor wider than dividend
Reg#(Bit#(100)) a5 <- mkReg(633825300114114700748351615033);
Reg#(Bit#(128)) b5 <- mkReg(1267650600228229401496703205383);

// wide / wide, dividend wider than divisor -- this one used to hang
Reg#(Bit#(128)) a6 <- mkReg(170141183460469231731687303715884105727);
Reg#(Bit#(100)) b6 <- mkReg(1180591620717411303431);

Reg#(Bool) done <- mkReg(False);

rule test (!done);
  $display("64/8    q=%h r=%h", primQuot(a1, b1), primRem(a1, b1));
  $display("96/96   q=%h r=%h", primQuot(a2, b2), primRem(a2, b2));
  $display("100/32  q=%h r=%h", primQuot(a3, b3), primRem(a3, b3));
  $display("32/100  q=%h r=%h", primQuot(a4, b4), primRem(a4, b4));
  $display("100/128 q=%h r=%h", primQuot(a5, b5), primRem(a5, b5));
  $display("128/100 q=%h r=%h", primQuot(a6, b6), primRem(a6, b6));
  done <= True;
endrule

rule quit (done);
  $finish(0);
endrule

endmodule
