import OInt::*;

// test operations on undefined integers
// for a range of types
// basically we should not crash
Integer i = ?;

(* synthesize *)
module sysUndefinedInteger(Empty);

  Reg#(Bool) gt <- mkReg(i > 0);
  Reg#(Bool) lt <- mkReg(i < 17);
  Reg#(Bool) eq <- mkReg(i == 99);
  Reg#(Bit#(32)) id <- mkReg(fromInteger(i));
  Reg#(UInt#(15)) plus <- mkReg(fromInteger(i+1));
  Reg#(OInt#(9)) sub <- mkReg(fromInteger(i-3));
  Reg#(Int#(17)) neg <- mkReg(fromInteger(-i));

endmodule

