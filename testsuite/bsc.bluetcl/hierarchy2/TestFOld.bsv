
import FIFO::*;
import Vector::*;

// Hierarchy test for virtual class
typedef UInt#(14) I;
typedef UInt#(14) O;
typedef 3   SIZE;

(*synthesize, options ="-elab"*)
module sysTestFOld ();
   for (Integer j=0 ; j <2; j = j + 1) begin
      Vector#(SIZE,Reg#(I)) rsssss ;
      for (Integer i = 0; i < valueOf(SIZE) ; i = i + 1) begin
         rsssss[i] <- mkRegU;
      end
   end

endmodule
