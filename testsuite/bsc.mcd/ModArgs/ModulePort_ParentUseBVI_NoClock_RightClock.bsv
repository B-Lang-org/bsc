
(* synthesize *)
module sysModulePort_ParentUseBVI_NoClock_RightClock ();
   Empty i1 <- mkSub (17);
endmodule

import "BVI"
module mkSub #(Bit#(32) x) ();
   port X clocked_by(no_clock) = x;
endmodule

