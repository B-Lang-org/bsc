import Vector::*;

typedef 512 Size;
typedef TLog#(Size) LSize;
Integer size = valueOf(Size);

(* synthesize *)
module sysConflictFreeNotOKLarge();


  Vector#(Size, Reg#(Bit#(19))) rs = ?;
  for (Integer i = 0; i < size; i = i + 1)
    rs[i] <- mkReg(0);

  Reg#(Bit#(LSize)) i <- mkReg(0);

  (* execution_order = "exit,r1,r2,r3" *)
  (* conflict_free="r1,r2,r3" *)
  rule r1;
    rs[i] <= rs[i] + zeroExtend(i);
  endrule

  rule r2;
    rs[i] <= rs[i] + 2;
  endrule
  
  rule r3;
    rs[i-1] <= rs[i-1] * 2;
  endrule

  rule exit(i > 1);
    $finish(0);
  endrule

  rule inc;
   $display("Incrementing i to %0d", i+1);
   i <= i + 1;
  endrule

endmodule
