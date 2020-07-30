//import GetPut::*;
//import ClientServer::*;
import FIFO::*;
//import Connectable::*;
import Vector::*;

// Hierarchy test for virtual class
typedef UInt#(14) I;
typedef UInt#(14) O;
typedef 3   SIZE;

(*synthesize, options ="-elab"*)
module sysSimpleLoop ();

   for (Integer i = 0; i < valueOf(SIZE) ; i = i + 1) begin
      Reg#(I) rsssss  <- mkRegU;

   end
endmodule
