
(* synthesize *)
module sysModulePort_ParentUseBVI_NoReset_WrongReset ();
   Reg#(Bit#(32)) x <- mkReg(0);
   Empty i1 <- mkSub (x);
endmodule

import "BVI"
module mkSub #(Bit#(32) x) ();
   port X reset_by(no_reset) = x;
endmodule

