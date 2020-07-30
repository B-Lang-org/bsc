import Connectable::*;
import GetPut::*;
import FIFO::*;

module mkTest();
   
   FIFO#(Bit#(32)) f <- mkFIFO;
   FIFO#(UInt#(64)) g <- mkFIFO;
   
   mkConnection(toPut(f), toGet(g));

endmodule
