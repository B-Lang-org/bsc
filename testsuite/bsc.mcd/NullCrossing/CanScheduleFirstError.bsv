(* synthesize *)
module sysCanScheduleFirstError();

   Reg#(UInt#(4)) x <- mkReg(0);
   
   (* can_schedule_first *)
   rule incr;
      x <= x + 1;
   endrule: incr
   
   // this rule must precede the write in incr, so incr's pragma
   // is not satisfied.
   rule done (x > 10);
      $finish(0);
   endrule: done
   
endmodule: sysCanScheduleFirstError