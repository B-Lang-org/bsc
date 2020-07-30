`include "subdir/defines2"

(* synthesize *)
module sysIncludeSubdir(Reg#(Bool));
   Reg#(Bool) rg <- message(`V, mkRegU);
   return rg;
endmodule

