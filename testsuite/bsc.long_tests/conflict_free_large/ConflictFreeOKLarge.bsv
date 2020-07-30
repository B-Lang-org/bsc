import Vector::*;

typedef 512 Size;
typedef TLog#(Size) LSize;
Integer size = valueOf(Size);

(* synthesize *)
module sysConflictFreeOKLarge();


  Vector#(Size, Reg#(Bit#(19))) rs = ?;
  for (Integer i = 0; i < size; i = i + 1)
    rs[i] <- mkReg(0);

  Reg#(Bit#(LSize)) i <- mkReg(0);

  Reg#(Bool) done <- mkReg(False);

  (* execution_order = "print_regs,r1,r2,r3" *)
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

  rule print_regs(i == 0 && done);
    for(Integer j = 0; j < size; j = j + 1)
      $display("rs[%0d]: %0d", j, rs[j]);
    $finish(0);
  endrule

  rule inc;
   done <= True;
   $display("Incrementing i to %0d", i+1);
   i <= i + 1;
  endrule

endmodule
