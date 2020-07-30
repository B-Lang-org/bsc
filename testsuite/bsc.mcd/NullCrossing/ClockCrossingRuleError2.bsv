(* synthesize *)
module sysClockCrossingRuleError2();

   Reg#(UInt#(4)) x <- mkReg(0);
   
   // this should fail because it may not fire when enabled
   (* clock_crossing_rule *)
   rule incr;
      x <= x + 1;
   endrule: incr
   
   (* descending_urgency = "decr7, incr" *)
   rule decr7 (x == 7);
      x <= x - 1;
   endrule: decr7
   
endmodule: sysClockCrossingRuleError2