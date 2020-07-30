import Clocks :: * ;

interface Ifc ;
   interface Clock clkOut ;
endinterface

// BSC should deduce that the missing gate of input clock 'c'
// must be "inhigh" (and not "unused")
(* synthesize *)
module sysPropDeduce_InClockAsOutClock#(Clock c) ( Ifc );
   interface clkOut = c ;
endmodule

/*
// If BSC deduced the above module correctly, this module should not compile
(* synthesize *)
module sysTest ();

   // Make a gated clock
   MakeClockIfc#(Bool) m <- mkClock(True, True);
   
   Ifc i <- sysPropDeduce_InClockAsOutClock(m.new_clk);
   
endmodule
*/
