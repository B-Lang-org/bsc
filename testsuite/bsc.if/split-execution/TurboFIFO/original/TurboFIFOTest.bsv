import FIFO::*;
import TurboFIFO::*;

(* synthesize *)
module sysTurboFIFOTest(Empty);
  
  Reg#(Bit#(16)) count <- mkReg(0);
  
  FIFO#(Bit#(16)) turbo <- mkTurboFIFO;

  rule enq(count < 10);
    turbo.enq(count);
    $display ("Enq %0d", count);
  endrule

  rule inc;
    $display ("Increment count %0d", count);
    count <= count + 1;
    if (count == 11) $finish(0);
  endrule

  rule deq(count != 5);
    $display("Deq %0d", turbo.first);
    turbo.deq;
  endrule

endmodule

  

