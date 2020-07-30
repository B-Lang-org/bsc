interface Sub;
   method UInt#(4) value();
endinterface

(* synthesize *)
module mkSub(Sub);
   
   Reg#(UInt#(4)) a <- mkReg(0);
   Wire#(UInt#(4)) w <- mkWire();

   // this rule must precede the value method
   rule r;
      w <= a;
      a <= a + 1;
   endrule
   
   method value = w;

endmodule: mkSub
   
(* synthesize *)
module sysCanScheduleFirstError2();

   Reg#(UInt#(4)) x <- mkReg(0);
   Sub sub <- mkSub();
   
   // this pragma is not satisfied because of the internal rule in sub
   (* can_schedule_first *)
   rule incr;
      x <= x + sub.value();
   endrule: incr
   
endmodule: sysCanScheduleFirstError2