`include "defines1"

(* synthesize *)
module sysIncludeNoPath(Reg#(Bool));
   Reg#(Bool) rg <- message(`V, mkRegU);
   return rg;
endmodule

