
import FIFO::*;
import Vector::*;

// Hierarchy test for virtual class
typedef UInt#(14) I;
typedef UInt#(14) O;
typedef 3   SIZE;

(*synthesize, options ="-elab"*)
module sysMultFor ();
   Vector#(TMul#(2,SIZE),Reg#(I)) rsssss ;
   for (Integer i = 0; i < valueOf(SIZE) ; i = i + 1) begin
      rsssss[i] <- mkRegU;
      rsssss[valueOf(SIZE)+i] <- mkRegU;
      
   end

endmodule
