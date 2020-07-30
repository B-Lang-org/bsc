
import GetPut:: *;
import FIFO :: *;
import Connectable :: * ;
import DReg::*;


(* synthesize *)
module sysTestToGPFunc ();

   FIFO#(int)  inf <- mkFIFO ;
   
   ActionValue#(int)  av = (
      actionvalue
         inf.deq;
         return inf.first;
      endactionvalue);

   let gf = toGet (av);

   Reg#(Bit#(10)) c <- mkReg(0);
   Reg#(int) d <- mkReg(0);

   function Action show (Bit#(10) cnt, int val);
      $display ( "%h: got data: %d", cnt, val);
   endfunction

   rule cnt ;
      c <= c + 1;
      if (c > 50) $finish(0);
   endrule

   rule inr ;
      inf.enq(d);
      d <= d + 1 ;
   endrule

   Put#(int) pifc = toPut ( when ( (c[2:0] <= 3), show(c) ));

   mkConnection (gf, pifc);

endmodule
