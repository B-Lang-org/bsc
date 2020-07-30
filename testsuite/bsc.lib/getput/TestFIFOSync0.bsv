
import GetPut:: *;
import FIFOF :: *;
import Connectable :: * ;
import Clocks :: * ;

(* synthesize *)
module sysTestFIFOSync0 ();
   
   let clk <- exposeCurrentClock;
   let rst <- exposeCurrentReset;
   let clk2 <- mkAbsoluteClock( 1,20);
   let rst2 <- mkAsyncReset( 2, rst, clk2 );
   
   SyncFIFOIfc#(void)  inf  <- mkSyncFIFO( 16, clk, rst, clk2) ;
   SyncFIFOIfc#(void)  outf <- mkSyncFIFO( 8, clk2, rst2, clk) ;
   
   Reg#(Bit#(10)) c <- mkReg(0);
   
   rule cnt ;
      c <= c + 1;
      if (c > 50) $finish(0);
   endrule
   
   rule inr (c[0:0] == 0);
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
