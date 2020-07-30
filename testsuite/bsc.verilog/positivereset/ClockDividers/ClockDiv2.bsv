
import Clocks :: * ;

(* synthesize *)
module sysClockDiv2() ;

   // Make a clock
   Clock clkA <- mkAbsoluteClock( 15,10 ) ;
   Reset rstA() ;
   mkAsyncResetFromCR#(3) iRstA( clkA, rstA ) ;
   
   // divide the clock
   ClockDividerIfc divClock <- mkClockDividerOffset( 8, 4, clocked_by(clkA), reset_by(rstA) ) ;
   Clock clkB = divClock.slowClock ;

   // We need a reset for the B domain as well
   Reset rstB <- mkAsyncReset(3, rstA, clkB) ;
   
   // Some counters for each clock
   Reg#(int)  areg <- mkReg(0, clocked_by clkA, reset_by rstA ) ;

   Reg#(int)  breg <- mkReg(0, clocked_by clkB, reset_by rstB ) ;

   // A register to do synchronized crossings
   Reg#(int)  crossreg <- mkSyncRegToSlow(0,  divClock, rstB ) ;

   // A register to do synchronized crossings
   Reg#(int)  crossregF() ;
   mkSyncRegToFast#(0)  icrossingRegF( divClock, rstB, crossregF ) ;

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
   rule aplus ( True ) ;
      areg <= areg + 1 ;
      $display("ap rl fired at %d, areg = %d creg = %d", adjusted_time(5), areg, crossregF ) ;
      if ( areg >= 1000) $finish(0) ;

   endrule

   rule trans ( True );
      $display("tr rl fired at %d, areg = %d" , adjusted_time(5), areg ) ;
      crossreg <= areg ;
   endrule

   // a rule to show the b clock
   rule b ( True ) ;
      breg <= breg + 1 ;
      $display("b rl fired at %d, breg = %d, crossReg = %d ", adjusted_time(40), breg, crossreg ) ;
      crossregF <= breg ;
      if ( breg >= 1000) $finish(0) ;
   endrule

   

endmodule
