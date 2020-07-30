import FIFOParam::*;
import FIFO::*;

(* synthesize *)
module sysZeroFIFOParamTest();
   
   FIFO#(Bit#(0)) f <- myZeroWidthFIFO(33);
   Reg#(Bit#(17)) deq_count <- mkReg(0);
   Reg#(Bit#(32)) enq_count <- mkReg(0);
   Reg#(Bit#(23)) cycle <- mkReg(0);
   
   rule tick;
      cycle <= cycle + 1;
   endrule
   
   rule deq(cycle > 40);
      $display("removing element at cycle %0d", cycle);
      $display("enq_count: %0d", enq_count);
      f.deq;
      deq_count <= deq_count + 1;
   endrule
   
   rule exit(deq_count == 10);
     $finish(0);
   endrule
   
   rule enq;
      f.enq(0);
      $display("adding element at cycle %0d", enq_count, cycle);
      enq_count <= enq_count + 1;
   endrule
   
 endmodule
