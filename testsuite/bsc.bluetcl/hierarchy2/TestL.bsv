import FIFO::*;
import List::*;

// Hierarchy test for virtual class
typedef UInt#(14) I;
typedef UInt#(14) O;
typedef 3   SIZE;

(*synthesize, options ="-elab"*)
module sysTestL ();
   List#(Reg#(I)) rsssss <- mapM( mkReg, map (fromInteger, (upto( 0, 3))));
endmodule

