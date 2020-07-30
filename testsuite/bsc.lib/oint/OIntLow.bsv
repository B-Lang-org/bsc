import OInt::*;

(* synthesize *)
module sysOIntBroken(Empty);

  Reg#(OInt#(2)) r <- mkReg(0);

  rule zero(r == 0);
     r <= -1;
  endrule

  rule one(r == -1);
     r <= 0;
     $finish(0);
  endrule

endmodule
    