
`ifndef FIFO_DEPTH 
`define FIFO_DEPTH 130
`endif



import Clocks :: *;
import FIFOLevel :: *;

(* synthesize *)
module sysFIFOCountTest () ;
   
   // Define a fifo of Int(#23) with 128 entries
   FIFOCountIfc#(UInt#(23),`FIFO_DEPTH) fifo 
                             <- mkFIFOCount ;

   // Define some constants 
   let almostFull = fifo.count > 120 ;
   let almostEmpty = fifo.count < 12 ;

   // a register to indicate a burst mode
   Reg#(Bool)  burstOut <- mkRegA( False ) ;
   Reg#(Bool)  dRunning <- mkRegA( False ) ;
   Reg#(Bool)  enqtoggle <- mkRegA( True ) ;
   
   Reg#(UInt#(32)) cycle <- mkRegA(0);
   Reg#(UInt#(23)) cnt <- mkRegA(0);
   
   rule stop;
      if (cycle>2000) $finish(0);
      cycle <= cycle+1;
   endrule

   rule enqueuetoggle (!enqtoggle);
      enqtoggle <= !enqtoggle;
   endrule
   rule enqueue (enqtoggle);
      enqtoggle <= !enqtoggle;
      fifo.enq(cnt);
      $display("%d: Enqueueing %d", cycle, cnt);
      cnt <= cnt+1;
   endrule
   
   (* descending_urgency="doClear, enqueue" *)
   rule doClear (cnt%400 == 299);
      $display ("%d clearing", cycle);
      fifo.clear;
      enqtoggle <= True ;
      cnt <= cnt + 1;
   endrule
   
   
   // Set and clear the burst mode depending on fifo status
   rule timeToDeque( almostFull && ! burstOut ) ;
      burstOut <= True ;
   endrule
//   (* descending_urgency="timeToDeque, moveData" *)
   rule moveData ( burstOut ) ;
      let dataToSend = fifo.first ;
      $display("%d dequeueing %d", cycle, dataToSend);
      fifo.deq ;
      burstOut <= ! almostEmpty ;
   endrule
   
   rule tests ;
      $display( "%d Count is %d", cycle, fifo.count );
   endrule

   
   
   //  type error since we require an Integer
//    rule testX ( ! fifo.levels.sIsLessThan( cnt ) )  ;
//       $display( "greater than 5 " ) ;
//    endrule
   
endmodule
