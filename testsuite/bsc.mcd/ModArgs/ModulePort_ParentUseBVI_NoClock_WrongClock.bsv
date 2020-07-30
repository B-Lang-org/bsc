
(* synthesize *)
module sysModulePort_ParentUseBVI_NoClock_WrongClock ();
   Reg#(Bit#(32)) x <- mkReg(0);
   Empty i1 <- mkSub (x);
endmodule

import "BVI"
module mkSub #(Bit#(32) x) ();
   port X clocked_by(no_clock) = x;
endmodule

