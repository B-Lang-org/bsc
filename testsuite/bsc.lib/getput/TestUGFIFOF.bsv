
import GetPut:: *;
import FIFOF :: *;
import Connectable :: * ;

(* synthesize *)
module sysTestUGFIFOF ();
   
   FIFOF#(int)  inf <- mkUGFIFOF ;
   FIFOF#(int)  outf <- mkUGFIFOF ;
   
   Reg#(Bit#(10)) c <- mkReg(0);
   Reg#(int) d <- mkReg(0);
   
   rule cnt ;
      c <= c + 1;
      if (c > 50) $finish(0);
   endrule
   
   rule inr (c[0:0] == 0 && inf.notFull);
      inf.enq(d);
      d <= d + 1 ;
   endrule
   
   rule outr (c[2:0] <= 3  && outf.notEmpty);
      outf.deq;
      $display( "%d: got data: %d", c, outf.first);
   endrule
   
   let gf = toGet (inf);
   let pf = toPut (outf);
   mkConnection( gf, pf);
   
endmodule
