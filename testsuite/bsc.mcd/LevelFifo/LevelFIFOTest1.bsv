
import LevelFIFO :: * ;
import LFSR :: * ;

import ConfigReg::*;

typedef Bit#(32)  Common ;

(* synthesize *)
module sysLevelFIFOTest1() ;
      
   // Some counters for each clock
   Reg#(Common)  areg <- mkReg(0) ;
   Reg#(Common)  breg <- mkReg(0) ;

   // An LFSR to generate random events
   LFSR#(Bit#(16)) lfsr <- mkLFSR_16 ;

   // The hardware under test -- a level fifo
   FIFOLevelIfc#(Common,128) fifo <- mkFIFOLevel ;
  
   // Define some constants 
   let fifoAlmostFull = fifo.isGreaterThan( 120 ) ;
   let fifoAlmostEmpty = fifo.isLessThan( 10 ) ;
  
   // a register to indicate a burst mode
   Reg#(Bool)  burstOut <- mkConfigReg( False ) ;

   // Set and clear the burst mode depending on fifo status
   rule dtimeToDeque( fifoAlmostFull && ! burstOut  ) ;
      $display( "%t: fifo almost full", $time ) ;
      burstOut <= True ;
   endrule  

   rule timeToStop ( fifoAlmostEmpty && burstOut );
      $display( "%t: fifo almost empty", $time ) ;
      burstOut <= False ;
   endrule

  
   rule moveData ( burstOut ) ;
      let dataToSend = fifo.first ;
      fifo.deq ;
      $display( "%t:  dequing data: %0d", $time, dataToSend ) ;
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



endmodule
