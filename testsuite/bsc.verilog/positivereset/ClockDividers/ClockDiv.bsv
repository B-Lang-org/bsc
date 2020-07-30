
import Clocks :: * ;

(* synthesize *)
module sysClockDiv() ;

   Reset resetin <- exposeCurrentReset ;

   // Make a clock
   Clock clkA <- mkAbsoluteClock( 15,10 ) ;
   Reset rstA() ;
   mkAsyncResetFromCR#(2) iRstA( clkA, rstA ) ;
   
   // divide the clock
   ClockDividerIfc divClock() ;
   mkClockDividerOffset#( 3, 0) iclkD(  clocked_by(clkA), divClock, reset_by(rstA) ) ;
   Clock clkB = divClock.slowClock ;

   // We need a reset for the B domain as well
   Reset rstB() ;
   mkAsyncReset#(2) iRstB( rstA, clkB, rstB ) ;
   
   // Some counters for each clock
   Reg#(int)  areg();
   mkReg#(0) iareg(areg, clocked_by clkA, reset_by rstA ) ;

   Reg#(int)  breg();
   mkReg#(0) ibreg(breg, clocked_by clkB, reset_by rstB ) ;
   
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
      $display("a rl fired at %d, areg = %d ", adjusted_time(5), areg ) ;
      if ( areg >= 5000) $finish(0) ;
   endrule

   // a rule to show the b clock
   rule b ( True ) ;
      breg <= breg + 1 ;
      $display("b rl fired at %d, breg = %d ", adjusted_time(20), breg ) ;
   endrule

endmodule
