import List::*;

(* synthesize *)
module sysSelectClockUndefinedList();

  List#(Clock) l = cons(noClock, nil);
  
  Clock c = l[?];

  Reg#(Bool) r <- mkReg(False, clocked_by(c));

endmodule
