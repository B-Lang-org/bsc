import Vector::*;

(* synthesize *)
module sysConflictFreeOK();

  Vector#(8, Reg#(Bit#(19))) rs <- replicateM(mkReg(0));
  
  Reg#(Bit#(3)) i <- mkReg(0);

  (* conflict_free="r1,r2,r3" *)
  rule r1;
    rs[i] <= rs[i] + zeroExtend(i);
  endrule

  rule r2;
    rs[i+1] <= rs[i+1] + 2;
  endrule
  
  rule r3;
    rs[i-1] <= rs[i-1] * 2;
  endrule

  rule print_regs;
    for(Integer j = 0; j < 8; j = j + 1)
      $write("rs[%0d]: %0h ", j, rs[j]);
    $display;
    if(i + 1 == 0) $finish(0);
  endrule

  rule inc;
   i <= i + 1;
  endrule

endmodule
