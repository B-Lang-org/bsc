import Inout::*;
import Connectable::*;

(* synthesize *)
module mkRedoInoutConnect#(Inout#(UInt#(32)) a, Inout#(UInt#(32)) b)();

  mkConnection(a,b);

endmodule
