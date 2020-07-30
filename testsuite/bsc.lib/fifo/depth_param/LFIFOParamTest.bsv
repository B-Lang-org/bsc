import FIFOParam::*;
import FIFO::*;

(* synthesize *)
module sysLFIFOParamTest();
   
   FIFO#(Bit#(32)) f <- myLSizedFIFO(5);
   Reg#(Bit#(17)) deq_count <- mkReg(0);
   Reg#(Bit#(32)) enq_count <- mkReg(0);
   Reg#(Bit#(23)) cycle <- mkReg(0);
   
   rule tick;
      cycle <= cycle + 1;
   endrule
   
   rule deq(cycle > 20);
      $display("removing element %0d at cycle %0d", f.first, cycle);
      $display("enq_count: %0d", enq_count);
      f.deq;
      deq_count <= deq_count + 1;
   endrule
   
   rule exit(deq_count == 10);
     $finish(0);
   endrule
   
   rule enq;
      f.enq(enq_count);
      $display("adding element %0d at cycle %0d", enq_count, cycle);
      enq_count <= enq_count + 1;
   endrule
   
 endmodule
