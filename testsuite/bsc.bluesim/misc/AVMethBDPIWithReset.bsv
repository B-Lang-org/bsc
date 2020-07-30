
// Test for a bug that occurred in Bluesim linking when an ActionValue method
// at a synthesis boundary was returning a value that was guarded by a reset.
// (Foreign functions are guarded by reset.)

import "BDPI"
function ActionValue #(Bit #(32)) c_func ();

interface Ifc;
   method ActionValue #(Bit #(32)) m ();
endinterface

(* synthesize *)
module sysAVMethBDPIWithReset (Ifc);

   Reg #(Bool)  rg_initialized <- mkReg (False);

   method ActionValue #(Bit #(32)) m  () if (rg_initialized);
      let x <- c_func ();
      return x;
   endmethod
endmodule

