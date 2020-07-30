import RAM::*;
import FIFO::*;
import FIFOF::*;
import GetPut::*;
import ClientServer::*;
import Common::*;

// First example of a processor (using an interface argument)
(* descending_urgency="start_fetch, start_load" *)
module mkProc1#(RAM#(Addr,Data) ram)(Processor);

   // RAM response arbitration (1-element pipeline FIFO)     
   FIFO#(RamUser) responseOwner <- mkLFIFO;
   
   // fetch state
   Reg#(Addr) pc <- mkReg(0);

   FIFOF#(Data) instrFIFO <- mkFIFOF;
   
   Bool fetchReady = instrFIFO.notFull;
   
   // rules directly use the RAM   
   rule start_fetch(fetchReady); 
      ram.request.put(Read(pc));
      responseOwner.enq(Fetch);
      pc <= pc + 1;
   endrule
   
   Bool fetchWaiting = responseOwner.first == Fetch;
   
   rule complete_fetch(fetchWaiting);
      let instr <- ram.response.get;
      instrFIFO.enq(instr);
      responseOwner.deq;
   endrule
   
   Bool loadReady = isMemoryInstr(instrFIFO.first);
   
   rule start_load(loadReady);
      instrFIFO.deq;
      ram.request.put(Read(17));
      responseOwner.enq(Load);
   endrule
   
   Bool loadWaiting = responseOwner.first == Load;
   
   Reg#(Bool) done <- mkReg(False);
   
   rule complete_load(loadWaiting);
      let data <- ram.response.get;
      responseOwner.deq;
      $display("Loaded data %h from RAM at time %0t", data, $time);
      done <= True;
   endrule
   
   method halt = done;
   
endmodule

(* synthesize *) 
module mkProc1_TB();
   let ram <- mkSimpleRAM;
   let proc <- mkProc1(ram);
   
   rule exit(proc.halt);
      $display("Processor halted at time %0t", $time);
      $finish(0);
   endrule
   
endmodule
