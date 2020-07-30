
`ifndef FIFO_DEPTH 
`define FIFO_DEPTH 128
`endif

import Clocks :: *;
import FIFOLevel :: *;

typedef `FIFO_DEPTH FIFO_DEPTH;

(* synthesize *)
module sysSyncFIFOCountTest () ;
   Clock clk <- exposeCurrentClock ;
   Reset rst <- exposeCurrentReset ;
   
   Clock  clk2 <- mkAbsoluteClock( 12, 13 );
   Reset  rst2 <- mkAsyncResetFromCR(1, clk2);
   
   // Define a fifo of Int(#23) with 128 entries
   SyncFIFOCountIfc#(UInt#(23),FIFO_DEPTH) fifo 
                             <- mkSyncFIFOCount(  clk, rst, clk2 ) ;

   // Define some constants 
   let sAlmostFull = fifo.sCount > 120 ;
   let dAlmostFull = fifo.dCount > 120 ;
   let dAlmostEmpty = fifo.dCount < 12 ;

   // a register to indicate a burst mode
   Reg#(Bool)  burstOut <- mkRegA( False, clocked_by clk2, reset_by rst2 ) ;
   Reg#(Bool)  dRunning <- mkRegA( False, clocked_by clk2, reset_by rst2 ) ;
   Reg#(Bool)  enqtoggle <- mkRegA( True ) ;
   
   Reg#(UInt#(32)) scycle <- mkRegA(0);
   Reg#(UInt#(32)) dcycle <- mkRegA(0, clocked_by clk2, reset_by rst2);
   Reg#(UInt#(23)) cnt <- mkRegA(0);
   
   rule stop;
      if (scycle>2000) $finish(0);
      scycle <= scycle+1;
   endrule

   rule dclkcnt ;
      dRunning <= True ;
      dcycle <= dcycle+1;
   endrule

   rule enqueuetoggle (!enqtoggle);
      enqtoggle <= !enqtoggle;
   endrule
   rule enqueue (enqtoggle);
      enqtoggle <= !enqtoggle;
      fifo.enq(cnt);
      $display("S %d: Enqueueing %d", scycle, cnt);
      cnt <= cnt+1;
   endrule
   
   (* descending_urgency="doClear, enqueue" *)
   rule doClear (cnt%400 == 299);
      $display ("S: %d clearing", scycle);
      fifo.sClear;
      enqtoggle <= True ;
      cnt <= cnt + 1;
   endrule
   
   
   rule doClearD (dcycle == 1200);
      $display ("D: %d clearing", dcycle);
      fifo.dClear;
   endrule
   
   
   // Set and clear the burst mode depending on fifo status
   rule timeToDeque( dAlmostFull && ! burstOut ) ;
      burstOut <= True ;
   endrule
   rule timeToStop ( dAlmostEmpty && burstOut );
      burstOut <= False ;
   endrule
   (* descending_urgency="timeToDeque, timeToStop, moveData" *)
   rule moveData ( burstOut ) ;
      let dataToSend = fifo.first ;
      $display("D: %d dequeueing %d", dcycle, dataToSend);
      fifo.deq ;
      // bursting.send( dataToSend ) ; 
   endrule
   
   rule tests ;
      $display( "S: %d sCount is %d", scycle, fifo.sCount );
   endrule
   rule testd (dRunning);
      $display( "D: %d dCount is %d", dcycle, fifo.dCount );
   endrule
   
   
   //  type error since we require an Integer
//    rule testX ( ! fifo.levels.sIsLessThan( cnt ) )  ;
//       $display( "greater than 5 " ) ;
//    endrule
   
endmodule
