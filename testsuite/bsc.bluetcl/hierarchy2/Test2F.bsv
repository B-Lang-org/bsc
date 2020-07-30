import FIFO::*;
import Vector::*;

// Hierarchy test for virtual class
typedef UInt#(14) I;
typedef UInt#(14) O;
typedef 3   SIZE;
typedef 5   OSIZE;

(*synthesize, options ="-elab"*)
module sysTest2F ();
   Vector#(OSIZE,Vector#(SIZE,Reg#(I))) rsssss ;
   for (Integer i = 0; i < valueOf(OSIZE) ; i = i + 1) begin
      for (Integer j = 0; j < valueOf(SIZE) ; j = j + 1) begin
         rsssss[i][j] <- mkRegU;
      end
   end
endmodule
