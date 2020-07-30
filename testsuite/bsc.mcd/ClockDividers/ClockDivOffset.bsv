import Clocks :: * ;

(* synthesize *)
module sysClockDivOffset() ;

   ClockDividerIfc clkDA <- mkClockDivider( 5 ) ;
   ClockDividerIfc clkDB <- mkClockDividerOffset( 5, 1  ) ;
   ClockDividerIfc clkDC <- mkClockDividerOffset( 5, 2  ) ;
   ClockDividerIfc clkDD <- mkClockDividerOffset( 5, 3  ) ;

   Clock clkA = clkDA.slowClock ;
   Clock clkB = clkDB.slowClock ;
   Clock clkC = clkDC.slowClock ;
   Clock clkD = clkDD.slowClock ;

   Reset rstA <- mkAsyncResetFromCR(2, clkA ) ;
   Reset rstB <- mkAsyncResetFromCR(2, clkB ) ;
   Reset rstC <- mkAsyncResetFromCR(2, clkC ) ;
   Reset rstD <- mkAsyncResetFromCR(2, clkD ) ;

   
   Reg#(int) ra <- mkReg(0, clocked_by clkA, reset_by rstA ) ;
   Reg#(int) rb <- mkReg(0, clocked_by clkB, reset_by rstB ) ;
   Reg#(int) rc <- mkReg(0, clocked_by clkC, reset_by rstC ) ;
   Reg#(int) rd <- mkReg(0, clocked_by clkD, reset_by rstD ) ;

   function ActionValue#(Bit#(64)) adjusted_time(Bit#(64) dummy);
   actionvalue
     let t <- $time;
     if (genVerilog)
       return (t + 30);
     else
       return t;
   endactionvalue
   endfunction

   rule aa ( True ) ;
      ra <= ra + 1 ;
      $display( "%t, Rule aa fired", adjusted_time(0) ) ;
   endrule
   rule bb ( True ) ;
      rb <= rb + 1 ;
      $display( "%t, Rule bb fired", adjusted_time(0) ) ;
   endrule
   rule cc ( True ) ;
      rc <= rc + 1 ;
      $display( "%t, Rule cc fired", adjusted_time(0) ) ;
   endrule
   rule dd ( True ) ;
      rd <= rd + 1 ;
      $display( "%t, Rule dd fired", adjusted_time(0) ) ;
      if ( rd > 10 ) $finish(0) ;
   endrule
   
endmodule
