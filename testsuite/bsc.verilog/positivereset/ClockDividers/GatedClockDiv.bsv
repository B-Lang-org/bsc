
import Clocks :: * ;

(* synthesize *)
module sysGatedClockDiv() ;

   Reset resetin <- exposeCurrentReset ;

   // Make a clock
   MakeClockIfc#(Bool) mk_clkA <- mkClock(False, True);
   Clock clkA = mk_clkA.new_clk;

   Reset rstA <- mkAsyncResetFromCR(2, clkA);
   
   // divide the clock
   ClockDividerIfc divClock <- mkGatedClockDivider(3, clocked_by clkA, reset_by rstA);
   Clock clkB = divClock.slowClock ;

   // We need a reset for the B domain as well
   Reset rstB <- mkAsyncReset(2, rstA, clkB);
   
   // Counters to generate clkA and its gate
   Reg#(int) clk_cntr <- mkReg(0);
   Reg#(int) gate_cntr <- mkReg(0);

   // Some counters for each clock
   Reg#(int) areg <- mkReg(0, clocked_by clkA, reset_by rstA) ;

   Reg#(int) breg <- mkReg(0, clocked_by clkB, reset_by rstB);

   // a rule to generate clkA and its gate
   rule gen_clk;
     mk_clkA.setClockValue(((clk_cntr > 3) && (clk_cntr < 7)) ||
                           (clk_cntr == 9) ||
                           (clk_cntr > 11));
     mk_clkA.setGateCond((gate_cntr < 21) || (gate_cntr > 53));
     if (clk_cntr == 13)
       clk_cntr <= 0;
     else
       clk_cntr <= clk_cntr + 1;
     if (gate_cntr == 79)
       gate_cntr <= 0;
     else
       gate_cntr <= 0;
   endrule
   
   // a rule to show the a clock
   rule a ( True ) ;
      areg <= areg + 1 ;
      $display("a rl fired at %d, areg = %d ", $time, areg ) ;
      if ( areg >= 5000) $finish(0) ;
   endrule

   // a rule to show the b clock
   rule b ( True ) ;
      breg <= breg + 1 ;
      $display("b rl fired at %d, breg = %d ", $time, breg ) ;
   endrule

endmodule
