// an apparent "swap" that is OK because the rules are CF

import Vector::*;

(* conflict_free = "rs_x, x_rs" *)
(* synthesize *)
module sysConflictFreeSwap();

  Reg#(UInt#(8)) j <- mkReg(0);

  Reg#(Bool) x <- mkReg(True);

  Vector#(64, Reg#(Bool)) rs = ?;

  for(Integer i = 0; i < 64; i = i + 1)
  begin
    rs[i] <- mkReg(False);
  end  

  rule rs_x;
    rs[j+1] <= x;
  endrule

  // to force ordering
  rule bogus;
     for(Integer i = 0; i < 64; i = i + 1)
       rs[i] <= rs[i];
  endrule

  rule x_rs;
    x <= rs[j];
  endrule

endmodule
