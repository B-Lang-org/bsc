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
module mkMid(Sub);
   Sub sub <- mkSub();

   method UInt#(4) value();
      return sub.value();
   endmethod
   
endmodule: mkMid
   
(* synthesize *)
module sysCanScheduleFirstError3();

   Reg#(UInt#(4)) x <- mkReg(0);
   Sub mid <- mkMid();
   
   // this pragma is not satisfied because of the internal rule in mid.sub
   (* can_schedule_first *)
   rule incr;
      x <= x + mid.value();
   endrule: incr
   
endmodule: sysCanScheduleFirstError3