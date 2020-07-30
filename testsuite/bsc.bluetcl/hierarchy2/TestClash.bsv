import GetPut::*;
import ClientServer::*;
import FIFO::*;
import Connectable::*;
import Vector::*;

// Hierarchy test for virtual class
typedef UInt#(14) I;
typedef UInt#(14) O;
typedef 3   SIZE;


(*synthesize, options ="-elab"*)
module sysTestClash ();
   FIFO#(I) inf <- mkFIFO;
   FIFO#(O) outf <- mkFIFO;

   ClientServer#(I,O) cs <- mkRequestResponseBuffer1;
   let c1 <- mkConnection(tpl_2(cs), fifosToClient(inf, outf));

endmodule
