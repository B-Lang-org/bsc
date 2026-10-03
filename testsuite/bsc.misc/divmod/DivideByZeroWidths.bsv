// Check that a runtime divide-by-zero yields all ones at every width,
// on both the narrow (<= 64 bit) and wide (> 64 bit) Bluesim paths.
// The widths 65, 70 and 100 are deliberately not multiples of the
// 32-bit word size, to exercise the masking of the top partial word.
//
// Bluesim only: the Verilog backend produces x for all of these.

module sysDivideByZeroWidths();

// The divisors live in registers so that they are not constant-folded,
// which would turn these into elaboration-time errors instead.
Reg#(UInt#(8))   z8   <- mkReg(0);
Reg#(UInt#(16))  z16  <- mkReg(0);
Reg#(UInt#(32))  z32  <- mkReg(0);
Reg#(UInt#(64))  z64  <- mkReg(0);
Reg#(UInt#(65))  z65  <- mkReg(0);
Reg#(UInt#(70))  z70  <- mkReg(0);
Reg#(UInt#(100)) z100 <- mkReg(0);
Reg#(UInt#(128)) z128 <- mkReg(0);

// Non-zero divisors, to confirm ordinary division still works.
Reg#(UInt#(32))  d32  <- mkReg(7);
Reg#(UInt#(100)) d100 <- mkReg(7);

Reg#(Bool) done <- mkReg(False);

rule test (!done);
  $display("q8    %h", UInt#(8)'(200)     / z8);
  $display("r8    %h", UInt#(8)'(200)     % z8);
  $display("q16   %h", UInt#(16)'(1203)   / z16);
  $display("r16   %h", UInt#(16)'(1203)   % z16);
  $display("q32   %h", UInt#(32)'(123456) / z32);
  $display("r32   %h", UInt#(32)'(123456) % z32);
  $display("q64   %h", UInt#(64)'(999999) / z64);
  $display("r64   %h", UInt#(64)'(999999) % z64);
  $display("q65   %h", UInt#(65)'(12345)  / z65);
  $display("r65   %h", UInt#(65)'(12345)  % z65);
  $display("q70   %h", UInt#(70)'(12345)  / z70);
  $display("r70   %h", UInt#(70)'(12345)  % z70);
  $display("q100  %h", UInt#(100)'(12345) / z100);
  $display("r100  %h", UInt#(100)'(12345) % z100);
  $display("q128  %h", UInt#(128)'(12345) / z128);
  $display("r128  %h", UInt#(128)'(12345) % z128);
  $display("ok32  %d %d", UInt#(32)'(123456) / d32, UInt#(32)'(123456) % d32);
  $display("ok100 %d %d", UInt#(100)'(12345) / d100, UInt#(100)'(12345) % d100);
  done <= True;
endrule

rule quit (done);
  $finish(0);
endrule

endmodule
