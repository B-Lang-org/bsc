import RAM::*;
import FIFO::*;
import FIFOF::*;
import GetPut::*;
import ClientServer::*;
import Common::*;

// extra libraries
import Connectable::*;
import SpecialFIFOs::*;

interface ProcWithRAMclient;
   // need to add a field to stand in for the ifc arg
   interface RAMclient#(Addr,Data) ramIn;
   interface Processor proc;
endinterface
             
// Second example of a processor
// uses RAMclient to avoid an interface argument
(* synthesize *)      
(* descending_urgency="start_fetch, start_load" *)
module mkProc2(ProcWithRAMclient);

   // RAM response arbitration (1-element pipeline FIFO)     
   FIFO#(RamUser) responseOwner <- mkLFIFO;
   
   // requires a BypassFIFO to avoid extra latency
   // requires extra state
   // could use more complex workarounds to eliminate it
   FIFO#(RAMreq#(Addr,Data)) requestFIFO <- mkBypassFIFO;
   // also requires a BypassFIFO to avoid extra latency
   // requires extra state (unless you use further workarounds)
   FIFO#(Data) responseFIFO <- mkBypassFIFO;
	 
   // fetch state
   Reg#(Addr) pc <- mkReg(0);

   FIFOF#(Data) instrFIFO <- mkFIFOF;
   
   Bool fetchReady = instrFIFO.notFull;
   
   // rules touch the RAM through extra FIFOs
   rule start_fetch(fetchReady); 
      requestFIFO.enq(Read(pc));
      responseOwner.enq(Fetch);
      pc <= pc + 1;
   endrule
   
   Bool fetchWaiting = responseOwner.first == Fetch;
   
   rule complete_fetch(fetchWaiting);
      let instr = responseFIFO.first;
      responseFIFO.deq;
      instrFIFO.enq(instr);
      responseOwner.deq;
   endrule
   
   Bool loadReady = isMemoryInstr(instrFIFO.first);
   
   rule start_load(loadReady);
      instrFIFO.deq;
      requestFIFO.enq(Read(17));
      responseOwner.enq(Load);
   endrule
   
   Bool loadWaiting = responseOwner.first == Load;
   
   Reg#(Bool) done <- mkReg(False);
   
   rule complete_load(loadWaiting);
      let data = responseFIFO.first;
      responseFIFO.deq;
      responseOwner.deq;
      $display("Loaded data %h from RAM at time %0t", data, $time);
      done <= True;
   endrule
   
   interface Processor proc;
     method halt = done;
   endinterface

   // have to hook up FIFOs to extra interface field
   interface RAMclient ramIn;
      interface request = toGet(requestFIFO);
      interface response = toPut(responseFIFO);
   endinterface
	 
endmodule

(* synthesize *)
module mkProc2_TB();

  let proc <- mkProc2;
  let ram <- mkSimpleRAM;
 
  mkConnection(proc.ramIn, ram);

  rule exit(proc.proc.halt);
     $display("Processor halted at time %0t", $time);
     $finish(0);
  endrule

endmodule
