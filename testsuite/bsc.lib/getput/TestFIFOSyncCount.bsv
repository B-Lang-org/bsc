
import GetPut:: *;
import FIFOLevel :: *;
import Connectable :: * ;

(* synthesize *)
module sysTestFIFOSyncCount ();
   
   let clk <- exposeCurrentClock ;
   let rst <- exposeCurrentReset ;
   
   SyncFIFOCountIfc#(int, 4)  inf <- mkSyncFIFOCount( clk, rst, clk ) ;
   SyncFIFOCountIfc#(int, 16)  outf <- mkSyncFIFOCount ( clk, rst, clk);
   
   Reg#(Bit#(10)) c <- mkReg(0);
   Reg#(int) d <- mkReg(0);
   
   rule cnt ;
      c <= c + 1;
      if (c > 50) $finish(0);
   endrule
   
   rule inr (c[0:0] == 0 && (inf.sCount < 3)) ;
      inf.enq(d);
      d <= d + 1 ;
   endrule
   
   rule outr (c[2:0] <= 3);
      outf.deq;
      $display( "%d: got data: %d", c, outf.first);
   endrule
   
   let gf = toGet (inf);
   let pf = toPut (outf);
   mkConnection( gf, pf);
   
endmodule
