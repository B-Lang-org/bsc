
(* synthesize *)
module sysModulePort_ParentUseBVI_NoReset_RightReset ();
   Empty i1 <- mkSub (17);
endmodule

import "BVI"
module mkSub #(Bit#(32) x) ();
   port X reset_by(no_reset) = x;
endmodule

