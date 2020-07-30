import Vector::*;

// vectors that pack to zero bits
(* synthesize *)
module sysZeroVector();


  Reg#(Vector#(0, Bit#(32))) r0 <- mkRegU;

  Reg#(Vector#(5, PrimUnit)) rU <- mkReg(replicate(tagged PrimUnit {}));

  Reg#(Vector#(0, Bit#(0)))  r00 <- mkReg(replicate(0));

  Vector#(0, Reg#(Bit#(32))) rV <- replicateM(mkReg(0));

  rule test;
    $display("r0: %0d", r0);
    $display("rU: %0d %0d %0d %0d %0d", rU[0], rU[1], rU[2], rU[3], rU[4]);
    $display("r00: %0d", r00);
    $finish(0);
  endrule

endmodule
