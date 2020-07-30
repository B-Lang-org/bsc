import OInt::*;

(* synthesize *)
module sysOIntHigh(Empty);

  Reg#(OInt#(2)) r <- mkReg(0);

  rule zero(r == 0);
     r <= 2;
  endrule

  rule two(r == 2);
     r <= 0;
     $finish(0);
  endrule

endmodule
    