import Clocks::*;

(* synthesize *)
module sysModulePort_ParentUseBVI_WrongReset ();

   Reset rst2 <- mkInitialReset(2);
   
   Reg#(Bit#(32)) x <- mkReg(0);

   Empty i <- mkSub (x, rst2);
endmodule

import "BVI"
module mkSub #(Bit#(32) x)
              (Reset r2, Empty i);
   input_reset rst2() = r2;
   port X reset_by(rst2) = x;
endmodule

