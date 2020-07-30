import RAM::*;
import GetPut::*;
import ClientServer::*;

typedef Bit#(32) Addr;
typedef Bit#(32) Data;
typedef Bit#(32) Instr;

typedef enum {Fetch, Load /* ... */} RamUser
  deriving(Eq,Bits); 

interface Processor;
   method Bool halt;
endinterface
          
// a RAM stub that just prints the address read
// and always returns 0 one cycle later
module mkSimpleRAM(RAM#(Addr,Data));
   Reg#(Bool) responseReady <- mkReg(False);
   
   // pretend the RAM can only handle one request at a time
   Bool ramAvailable = !responseReady;
   
   interface Put request;
      method Action put(r) if(ramAvailable);
        case (r) matches
	   tagged Read .addr: begin
	      $display("RAM read at address %h at time %0t", addr, $time);
	      responseReady <= True;
	   end
           tagged Write {.addr, .data}: begin
              $display ("ERROR: Writes not supported");
	      $finish(0);
           end
        endcase
      endmethod
   endinterface
   
   interface Get response;
      method ActionValue#(Data) get if(responseReady);
	 responseReady <= False;
	 return(0);
      endmethod
   endinterface
   
endmodule
      
// no real instruction encoding
function Bool isMemoryInstr(Instr i);
   return(True);
endfunction
