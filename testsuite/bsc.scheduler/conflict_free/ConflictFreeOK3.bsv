import Vector::*;
import FIFO::*;

(* synthesize *)
module sysConflictFreeOK3();

  Vector#(8, FIFO#(Bit#(16))) fs <- replicateM(mkFIFO);
  
  Reg#(Bit#(3)) i <- mkReg(0);

  rule enq_data;
    for(Integer j = 0; j < 8; j = j + 1) begin
      Bit#(16) v = zeroExtend(i) + fromInteger(j);   
      fs[j].enq(v*v);
    end
  endrule

  (* conflict_free="r1,r2,r3" *)
  rule r1;
    $display("r1 deq FIFO %0d",i);
    fs[i].deq;
  endrule

  rule r2;
    $display("r2 deq FIFO %0d",i+1);
    fs[i+1].deq;
  endrule
  
  rule r3(i == 4);
    // this won't execute because by the time 
    // i == 4, not all the FIFOs are full
    $display("r3");
    for(Integer j = 0; j < 8; j = j + 1)
      fs[j].deq;
  endrule

  for(Integer j = 0; j < 8; j = j + 1)
    rule print_data;
        $display("fs[%0d]: %0d", j, fs[j].first);
    endrule

  rule inc;
   if(i + 1 == 0) $finish(0);
   $display("Incrementing i to %0d", i+1);
   i <= i + 1;
  endrule

endmodule
