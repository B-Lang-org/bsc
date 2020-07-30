import BRAM::*;
import BRAMFIFO::*;
import StmtFSM::*;
import Clocks::*;

function BRAMRequest#(Bit#(8), Bit#(8)) makeRequest(Bool write, Bit#(8) addr, Bit#(8) data);
   return BRAMRequest{
		      write: write,
		      address: addr,
		      datain: data
		      };
endfunction

(* synthesize *)
module sysSyncBRAMFIFOToTest();
   
   let                                       rxclk               <- mkAbsoluteClock(1, 8);
   let                                       rxrst               <- mkAsyncResetFromCR(3, rxclk);
   
   SyncFIFOIfc#(Bit#(8))                     bram_fifo           <- mkSyncBRAMFIFOToCC(16, rxclk, rxrst);

   Stmt test =
   (seq
       $display("Starting Simulation");
    
       delay(30);
    
       repeat(16)
       action
	  bram_fifo.deq;
	  $display("data: %x", bram_fifo.first);
       endaction
       delay(30);
    
       repeat(16)
       action
	  bram_fifo.deq;
	  $display("data: %x", bram_fifo.first);
       endaction

       delay(1000);
       $display("Ending Simulation @ %t", $time);
    endseq);

   mkAutoFSM(test);
   
   Stmt enqueue =
   seq
      bram_fifo.enq(8'hFF);
      bram_fifo.enq(8'hFE);
      bram_fifo.enq(8'hFD);
      bram_fifo.enq(8'hFC);
      bram_fifo.enq(8'hFB);
      bram_fifo.enq(8'hFA);
      bram_fifo.enq(8'hF9);
      bram_fifo.enq(8'hF8);
      bram_fifo.enq(8'hF7);
      bram_fifo.enq(8'hF6);
      bram_fifo.enq(8'hF5);
      bram_fifo.enq(8'hF4);
      bram_fifo.enq(8'hF3);
      bram_fifo.enq(8'hF2);
      bram_fifo.enq(8'hF1);
      bram_fifo.enq(8'hF0);
      
      bram_fifo.enq(8'hEF);
      bram_fifo.enq(8'hEE);
      bram_fifo.enq(8'hED);
      bram_fifo.enq(8'hEC);
      bram_fifo.enq(8'hEB);
      bram_fifo.enq(8'hEA);
      bram_fifo.enq(8'hE9);
      bram_fifo.enq(8'hE8);
      bram_fifo.enq(8'hE7);
      bram_fifo.enq(8'hE6);
      bram_fifo.enq(8'hE5);
      bram_fifo.enq(8'hE4);
      bram_fifo.enq(8'hE3);
      bram_fifo.enq(8'hE2);
      bram_fifo.enq(8'hE1);
      bram_fifo.enq(8'hE0);
      delay(100000);
   endseq;
   
   mkAutoFSM(enqueue, clocked_by rxclk, reset_by rxrst);
   
endmodule
