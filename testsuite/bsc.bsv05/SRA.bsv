export mkSharedRAMArbiter;
export RAM;
			  
import Vector::*;
	      
import FIFO::*;
	     
interface RAM#(parameter type a, parameter type b);
    method Action send(a x1);
    method ActionValue#(b) receive;
endinterface: RAM
		 
module mkSharedRAMArbiter#(parameter (RAM#(a, b)) ram)(Vector#(n, RAM#(a, b)))
  provisos (Log#(n,k));
  FIFO#((Bit#(k))) tagFifo();
  mkFIFO the_tagFifo(tagFifo);
  module mkSharedRam#(parameter Integer i)(RAM#(a, b));
    method send(x);
	       action
		 tagFifo.enq(fromInteger(i)); ram.send(x);
	       endaction
    endmethod: send
    method receive() if (tagFifo.first == fromInteger(i));
	       actionvalue
		 tagFifo.deq; 
                 let result <- ram.receive;
                 return (result);
	       endactionvalue
    endmethod: receive
    
  endmodule: mkSharedRam
  Vector#(n, RAM#(a, b)) ifc <- mapM(mkSharedRam, genList);
  return(ifc);
endmodule: mkSharedRAMArbiter
			     
typedef  Bit#(16) Word;
		       
module mkArbiterTest(Empty);
  RAM#(Word, Word) sram();
  mkRAM the_sram(sram);
  Vector#(3, (RAM#(Word, Word))) rams();
  mkSharedRAMArbiter#(sram) the_rams(rams);
  mkContender(2, "1", rams[0]);
  mkContender(3, "2", rams[1]);
  mkContender(5, "3", rams[2]);
endmodule: mkArbiterTest
			
module mkContender#(parameter Word initial_request,
		    parameter String str,
		    parameter (RAM#(Word, Word)) ram)(Empty);
  Reg#((Maybe#(Word))) request();
  mkReg#(Valid(initial_request)) the_request(request);
  Reg#(Word) counter();
  mkReg#(0) the_counter(counter);
  Reg#(Word) counter_step();
  mkReg#(1) the_counter_step(counter_step);
  Reg#(Word) counter_last();
  mkReg#(1) the_counter_last(counter_last);
  // String name =  "User" +++ str;;
  rule do_Count; 
   counter <= counter + 1;
  endrule
  rule do_Request 
   (counter >= counter_last &&& request matches tagged Valid {.x});
      counter_step <= counter_step + 1;
      counter_last <= counter + counter_step;
      ram.send(x);
      request <= Invalid;
  endrule
  rule do_Receive; 
      Word res <- ram.receive;
      request <= Valid(res);
  endrule
  
endmodule: mkContender
		      
module mkRAM(RAM#(n, n)) provisos(Bits#(n,s), Arith#(n));
  FIFO#(n) incoming();
  mkFIFO the_incoming(incoming);
  FIFO#(n) outgoing();
  mkFIFO the_outgoing(outgoing);
  
  rule move;
    outgoing.enq(incoming.first); incoming.deq;
  endrule

  method send = incoming.enq;
  method receive();
	     actionvalue
	       outgoing.deq;
	       return(outgoing.first * 2);
	     endactionvalue
  endmethod: receive
  
endmodule: mkRAM
		


