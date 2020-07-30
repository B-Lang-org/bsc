
import GetPut:: *;
import FIFOLevel :: *;
import Connectable :: * ;

(* synthesize *)
module sysTestFIFOSyncLevel0 ();
   
   let clk <- exposeCurrentClock ;
   let rst <- exposeCurrentReset ;
   
   SyncFIFOLevelIfc#(void, 4)  inf <- mkSyncFIFOLevel( clk, rst, clk ) ;
   FIFOLevelIfc#(void, 12)  outf <- mkFIFOLevel ;
   
   Reg#(Bit#(10)) c <- mkReg(0);
   
   rule cnt ;
      c <= c + 1;
      if (c > 50) $finish(0);
   endrule
   
   rule inr (c[0:0] == 0 && inf.sIsLessThan(3)) ;
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
