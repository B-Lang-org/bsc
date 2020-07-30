
import GetPut:: *;
import FIFOLevel :: *;
import Connectable :: * ;

(* synthesize *)
module sysTestFIFOCount0 ();
   
   FIFOCountIfc#(void, 4)  inf <- mkFIFOCount ;
   FIFOCountIfc#(void, 12)  outf <- mkFIFOCount ;
   
   Reg#(Bit#(10)) c <- mkReg(0);
   
   rule cnt ;
      c <= c + 1;
      if (c > 50) $finish(0);
   endrule
   
   rule inr (c[0:0] == 0 && (inf.count < 3 ) );
      inf.enq(?);
   endrule
   
   rule outr (c[2:0] <= 3);
      outf.deq;
      $display( "%d: got data: %d", c, outf.first);
   endrule
   
   let gf = toGet (inf);
   let pf = toPut (outf);
   mkConnection( gf, pf);
   
endmodule
