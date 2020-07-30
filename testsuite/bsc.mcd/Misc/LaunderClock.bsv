import Clocks::*;

(* synthesize *)
module sysLaunderClock();
   Clock c <- mkAbsoluteClock(5, 17);
   
   LaunderClock lc_ifc <- mkLaunderClock(c);

   Clock lc = lc_ifc.laundered_clk;
   
   rule test;
      if(sameFamily(c, lc))
	 $display("Test Passed");
      else
	 $display("Test Failed");
      
      $finish(0);
   endrule   
   
endmodule

interface LaunderClock;
   interface Clock laundered_clk;
endinterface

(* synthesize *)
module mkLaunderClock#(Clock c)(LaunderClock);
   interface laundered_clk = c;
endmodule
   
