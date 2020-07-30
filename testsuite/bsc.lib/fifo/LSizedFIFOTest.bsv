import StmtFSM::*;
import FIFO::*;

Integer fifoSize = 65;

(* synthesize *)
module sysLSizedFIFOTest();
   
   FIFO#(Bit#(16)) f <- mkLSizedFIFO(fifoSize);
   
   Reg#(Bit#(16)) count <- mkReg(0);
   
   Bit#(16) tags[5] = {16'hdead, 16'hbeef, 16'hbaad, 16'hf00d, 16'h0 };
   
   Reg#(Bit#(16)) cycle <- mkReg(0);
   
   rule tick;
      cycle <= cycle + 1;
   endrule
      
   Stmt loadFifo = 
   seq 
      while(count < fromInteger(2*fifoSize))
	 action     
	    let val = tags[count % 5];
            $display("enq %h at cycle %0d", val, cycle);      
	    f.enq(val);
	    count <= count + 1;
	 endaction
   endseq;

   FSM loader <- mkFSM(loadFifo);

   rule startLoad;
      loader.start;
   endrule
   
   Reg#(Bit#(16)) deq_count <- mkReg(0);
   
   Stmt drainFifo = 
   seq
     while(deq_count < 20)
       action
         $display("Removing element %h at cycle %0d", f.first, cycle);
         f.deq;
         deq_count <= deq_count + 1;
       endaction
     $finish(0);
   endseq;

   FSM drainer <- mkFSM(drainFifo);
   
   rule startDrainer(cycle == fromInteger(fifoSize + 10));
     drainer.start;
   endrule

   rule clear(cycle == fromInteger(fifoSize + 20));
     $display("Clearing fifo at cycle %0d", cycle);
     f.clear;
   endrule
   
endmodule
   
	
