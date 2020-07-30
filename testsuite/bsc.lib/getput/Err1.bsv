
import GetPut:: *;
import FIFO :: *;
import Connectable :: * ;

(* synthesize *)
module sysFifo ();
   
   FIFO#(int)  inf <- mkFIFO ;
   FIFO#(Bit#(32))  outf <- mkFIFO ;
   
   Reg#(Bit#(10)) c <- mkReg(0);
   Reg#(int) d <- mkReg(0);
   
   rule cnt ;
      c <= c + 1;
      if (c > 50) $finish(0);
   endrule
   
   rule inr (c[0:0] == 0);
      inf.enq(d);
      d <= d + 1 ;
   endrule
   
   rule outr (c[2:0] <= 3);
      outf.deq;
      $display( "%d: got data: %d", c, outf.first);
   endrule
   
   Get#(int) gf = toGet (inf);
   Put#(int) pf = toPut (outf);
   mkConnection( gf, pf);
   
endmodule
