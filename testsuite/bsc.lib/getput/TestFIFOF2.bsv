
import GetPut:: *;
import FIFOF :: *;
import Connectable :: * ;

// instance ToGet#( Reg#(a), a )
//    provisos ( Arith#(a) );

//    function Get#(a) toGet ( Reg#(a) r );
//       return (interface Get#(a);
//                  method ActionValue#(a) get ;
//                     r <= r + 1;
//                     return r ;
//                  endmethod
//               endinterface);
//    endfunction
// endinstance


(* synthesize *)
module sysTestFIFOF2 ();
   
   FIFOF#(int)  inf <- mkFIFOF ;
   FIFOF#(int)  outf <- mkFIFOF ;
   
   Reg#(Bit#(10)) c <- mkReg(0);
   Reg#(int) d <- mkReg(0);

//   Get#(int) getd = toGet (asReg(d));
//   mkConnection (getd, toPut(inf) );
   let inf_p = toPut(inf);
   rule pushinf ;
      d <= d+1;
      inf_p.put(d);
   endrule
   
   rule cnt ;
      c <= c + 1;
      if (c > 50) $finish(0);
   endrule
      
   rule outr (c[2:0] <= 3);
      outf.deq;
      $display( "%d: got data: %d", c, outf.first);
   endrule
   
   let gf = toGet (inf);
   let pf = toPut (outf);
   mkConnection( gf, pf);
   
   
   
endmodule
