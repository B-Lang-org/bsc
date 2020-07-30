
import FIFO::*;
import Vector::*;

// Hierarchy test for virtual class
typedef UInt#(14) I;
typedef UInt#(14) O;
typedef 3   SIZE;

(*synthesize, options ="-elab"*)
module sysLoop2 ();

   for (Integer i = 0; i < valueOf(SIZE) ; i = i + 1) begin
      Reg#(I) aaa <- mkRegU;
   end
   
   for (Integer i = 0; i < valueOf(SIZE) ; i = i + 1) begin
      Reg#(O) bbb <- mkRegU;
   end
   
endmodule
