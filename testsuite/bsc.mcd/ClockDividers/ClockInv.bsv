
import Clocks :: * ;

(* synthesize *)
module sysClockInv() ;

   Reset resetin <- exposeCurrentReset ;

   // Make a clock
   Clock clkA <- mkAbsoluteClock( 15,10 ) ;
   Reset rstA() ;
   mkAsyncReset#(3) iRstA( resetin, clkA, rstA ) ;
   
   // divide the clock
   ClockDividerIfc divClock <- mkClockInverter( clocked_by clkA, reset_by rstA ) ;
   Clock clkB = divClock.slowClock ;

   // We need a reset for the B domain as well
   Reset rstB() ;
   mkAsyncReset#(3) iRstB( rstA, clkB, rstB ) ;
   
   // Some counters for each clock
   Reg#(int)  areg();
   mkReg#(0) iareg(areg, clocked_by clkA, reset_by rstA ) ;

   Reg#(int)  breg();
   mkReg#(0) ibreg(breg, clocked_by clkB, reset_by rstB ) ;

   // A register to do synchronized crossings
   Reg#(int)  crossreg() ;
   mkSyncReg#(0)  icrossingReg(clkA, rstA, clkB, crossreg ) ;


   // A register to do synchronized crossings
   Reg#(int)  crossregF() ;
   mkSyncReg#(0)  icrossingRegF(clkB, rstB, clkA, crossregF ) ;
   
   // We use a dummy argument to work around bug 1251
   function ActionValue#(Bit#(64)) adjusted_time(Bit#(8) dummy);
   actionvalue
     let t <- $time;
     if (genVerilog)
       return (t + 5);
     else
       return t;
   endactionvalue
   endfunction


   // a rule to show the a clock
   rule aplus ( True ) ;
      areg <= areg + 1 ;
      $display("ap rl fired at %d, areg = %d creg = %d", adjusted_time(0), areg, crossregF ) ;
      if ( areg >= 1000) $finish(0) ;

   endrule

   rule trans ( True );
      $display("tr rl fired at %d, areg = %d" , adjusted_time(0), areg ) ;
      crossreg <= areg ;
   endrule

   // a rule to show the b clock
   rule b ( True ) ;
      breg <= breg + 1 ;
      $display("b  rl fired at %d, breg = %d, crossReg = %d ", adjusted_time(0), breg, crossreg ) ;
      crossregF <= breg ;
      if ( breg >= 1000) $finish(0) ;
   endrule

endmodule

