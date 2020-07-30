
import GetPut:: *;
import FIFO :: *;
import Connectable :: * ;
import DReg::*;


(* synthesize *)
module sysTestToGPWire ();

   FIFO#(int)  inf <- mkFIFO ;
   Reg#(int)  outr <- mkWire ;

   let gf = toGet (inf);
   let pr = toPut (asReg(outr));
   let gr = toGet (asReg(outr));

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

   rule outrule (c > 5);
      let x <- gr.get ;
      $display( "%d: got data: %d", c, x);
   endrule

   mkConnection( gf, pr);

endmodule
