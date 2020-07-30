import Vector::*;
import FIFO::*;

(* options = "-aggressive-conditions" *)
(* synthesize *)
module sysConflictFreeOK2();

  Vector#(8, FIFO#(Bit#(19))) fs <- replicateM(mkFIFO);
  
  Reg#(Bit#(3)) i <- mkReg(0);

  (* conflict_free="r1,r2,r3" *)
  rule r1;
    $display("Enq %0d to FIFO %0d",i,i); 
    fs[i].enq(zeroExtend(i));
  endrule

  rule r2;
    $display("Enq %0d to FIFO %0d",i+1,i+1);
    fs[i+1].enq(zeroExtend(i+1));
  endrule
  
  rule r3;
    Bit#(19) val = 2*zeroExtend(i);
    $display("Enq %0d to FIFO %0d",val,i-1);
    fs[i-1].enq(val);
  endrule

  rule print_data;
    for(Integer j = 0; j < 8; j = j + 1)
      $display("fs[%0d]: %0d", j, fs[j].first);
    $finish(0);
  endrule

  rule inc;
   $display("Incrementing i to %0d",i+1);
   i <= i + 1;
  endrule

endmodule
