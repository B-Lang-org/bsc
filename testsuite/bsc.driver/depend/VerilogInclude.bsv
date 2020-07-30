`include "defines"

(* synthesize *)
module sysVerilogInclude(Reg#(Bool));
   Reg#(Bool) rg <- message(`V, mkRegU);
   return rg;
endmodule

