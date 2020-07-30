
import Clocks :: * ;

typedef Bit#(32)  Common ;

(* synthesize *)
module sysClockDivFifo() ;

   Reset resetin <- exposeCurrentReset ;

   // Make a clock
   Clock clkA <- mkAbsoluteClock( 15,10 ) ;
   Reset rstA() ;
   mkInitialReset#(5) iRstA( rstA, clocked_by clkA ) ;
   
   // divide the clock
   ClockDividerIfc divClock() ;
   mkClockDividerOffset#( 8, 2 ) iClkD( clocked_by(clkA), divClock, reset_by(rstA) ) ;
   Clock clkB = divClock.slowClock ;

   // We need a reset for the B domain as well
   Reset rstB() ;
   mkInitialReset#(3) iRstB( rstB, clocked_by clkB ) ;
   
   // Some counters for each clock
   Reg#(Common)  areg();
   mkReg#(0) iareg(areg, clocked_by clkA, reset_by rstA ) ;

   Reg#(Common)  breg();
   mkReg#(0) ibreg(breg, clocked_by clkB, reset_by rstB ) ;

   // A register to do synchronized crossings
   SyncFIFOIfc#(Common)  crossfifo() ;
   mkSyncFIFOToSlow#(4)  cFS( divClock, rstB, 
                                crossfifo ) ;

   // A register to do synchronized crossings
   SyncFIFOIfc#(Common)  crossfifoF() ;
   mkSyncFIFOToFast#(4)  cFF( divClock, rstB, 
                                crossfifoF ) ;

   function ActionValue#(Bit#(64)) adjusted_time(Bit#(64) lag);
   actionvalue
     let t <- $time;
     if (genVerilog)
       return (t + lag);
     else
       return t;
   endactionvalue
   endfunction

   // a rule to show the a clock
   rule a ( True ) ;
      areg <= areg + 1 ;
      $display("a  rl fired at %d, areg = %d ", adjusted_time(5), areg ) ;
      if ( areg >= 1000) $finish(0) ;

      crossfifo.enq( areg ) ;
   endrule

   rule a2 ( areg[0] == 0 ) ;
      crossfifoF.deq() ;
      $display("a2 rl fired at %d, areg = %d, fifoTF = %d", adjusted_time(5), areg, crossfifoF.first ) ;
   endrule

   // a rule to show the b clock
   rule b ( True ) ;
      breg <= breg + 1 ;
      if ( breg >= 1000) $finish(0) ;
   endrule

   rule b2 ( breg[0] == 0 );
      crossfifoF.enq(breg) ;
      $display("b2 rl fired at %d, breg = %d, ", adjusted_time(40), breg ) ;
   endrule

   // hold off fireing to let fifo fill
   rule b1 ( breg > 5 ) ;
      let cr = crossfifo.first ;  crossfifo.deq ;
      $display("b  rl fired at %d, breg = %d, crossfifoTS = %d ", adjusted_time(40), breg, cr ) ;
      
   endrule


endmodule
