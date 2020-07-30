
import LevelFIFO :: * ;
import Clocks :: * ;
import LFSR :: * ;

import ConfigReg::*;

typedef Bit#(32)  Common ;

(* synthesize *)
module sysSyncLevelFIFOTest() ;

   Reset resetin <- exposeCurrentReset ;
   
   // Make a clock
   Clock clkA <- mkAbsoluteClock( 15, 100 ) ;
   Reset rstA() ;
   mkAsyncReset#(5) iRstA( resetin, clkA, rstA ) ;
   
   // Make a second clock and reset
   Clock clkB <- mkAbsoluteClock( 15, 9 ) ;
   Reset rstB <- mkAsyncReset( 5, resetin, clkB ) ;

      
   // Some counters for each clock
   Reg#(Common)  areg <- mkReg(0, clocked_by clkA, reset_by rstA ) ;
   Reg#(Common)  breg <- mkReg(0, clocked_by clkB, reset_by rstB ) ;

   // An LFSR to generate random events
   LFSR#(Bit#(16)) lfsr <- mkLFSR_16( clocked_by clkA, reset_by rstA )  ;


   // The hardware under test -- a level fifo
   SyncFIFOLevelIfc#(Common,128) fifo <- mkSyncFIFOLevel(  clkA, rstA, clkB ) ;
  
   // Define some constants 
   let sFifoAlmostFull = fifo.sIsGreaterThan( 120 ) ;
   let dFifoAlmostFull = fifo.dIsGreaterThan( 120 ) ;
   let dFifoAlmostEmpty = fifo.dIsLessThan( 12 ) ;
   let sFifoAlmostEmpty = fifo.sIsLessThan( 110 ) ;
  
   // a register to indicate a burst mode
   Reg#(Bool)  burstOut <- mkConfigReg( False, clocked_by clkB, reset_by rstB ) ;
   Reg#(Bool)  pauseFill <- mkReg( False, clocked_by clkA, reset_by rstA ) ;
   

   // Set and clear the burst mode depending on fifo status
   rule dtimeToDeque( dFifoAlmostFull && ! burstOut  ) ;
      $display( "%t:  destination fifo almost full", $time ) ;
      burstOut <= True ;
   endrule  
      
   rule timeToStop ( dFifoAlmostEmpty && burstOut );
      $display( "%t:   destination clk fifo almost empty", $time ) ;
      burstOut <= False ;
   endrule

   rule stimeToDeque( sFifoAlmostFull && ! pauseFill ) ;
      pauseFill <= True ;
      $display( "%t:  source fifo almost full", $time ) ;
   endrule  
   rule stimeToStop ( sFifoAlmostEmpty && pauseFill );
      pauseFill <= False ;
      $display( "%t:  source fifo almost empty", $time ) ;
   endrule
  
   rule moveData ( burstOut ) ;
      let dataToSend = fifo.first ;
      fifo.deq ;
      $display( "%t:  dequing data: %0d", $time, dataToSend ) ;
   endrule

   rule dispNF ( ! fifo.sNotFull );
      $display( "%t:  fifo full", $time );
   endrule
   rule dispNE ( ! fifo.dNotEmpty );
      $display( "%t:  fifo empty", $time );
   endrule

   // a rule to show the a clock
   rule a ( True ) ;
      lfsr.next ;
      if ( lfsr.value[3:0] > 7 )      // half time fill up
         begin
            areg <= areg + 1 ;
            $display("%t:  enquing areg = %0d ", $time, areg ) ;
            fifo.enq( areg ) ;
            if ( areg >= 1000) $finish(0) ;
         end
   endrule
   
   (* descending_urgency = "doClear, a" *)
   rule doClear (lfsr.value % 400 == 299);
      lfsr.next ;
      $display ("%t clearing", $time);
      fifo.sClear;
   endrule
   
   

     
   

endmodule
