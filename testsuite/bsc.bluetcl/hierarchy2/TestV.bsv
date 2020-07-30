import FIFO::*;
import Vector::*;

// Hierarchy test for virtual class
typedef UInt#(14) I;
typedef UInt#(14) O;
typedef 3   SIZE;

(*synthesize, options ="-elab"*)
module sysTestV ();
   Vector#(SIZE,Reg#(I)) rsssss <- replicateM(mkRegU);
endmodule

