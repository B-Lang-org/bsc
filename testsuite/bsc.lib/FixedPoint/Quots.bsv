import FixedPoint::*;
import StmtFSM::*;
import FShow::*;

// Test types
typedef FixedPoint#(2,2)  TA;
typedef FixedPoint#(2,2)  TB;
typedef FixedPoint#(5,4)  FPQ1;
typedef FixedPoint#(5,2)  FPQ2;

typedef FixedPoint#(2,3)  TF;

typedef Int#(4) IA;
typedef Int#(3) IB;

// A print utility for debug
function Action printFixedPoint( String msg, Integer fwidth, FixedPoint#(i,f) a )
   provisos (
             Add#(i, f, TAdd#(i,f)),
             Add#(1, xxxA, i )
             ) ;
   action
      if (msg != "") $write("%s", msg);
      $write( "(%b.%b) ", fxptGetInt(a), fxptGetFrac(a) );
      fxptWrite( fwidth, a ) ;
   endaction
endfunction




(*synthesize*)
module sysQuots();

   let pfp = printFixedPoint("",4) ;  // rename a function to save typing !
   let pfp8 = printFixedPoint("",8) ;  // rename a function to save typing !
   let pfpS = fxptWrite( 4 ) ;

   Reg#(TA) ra <- mkReg(minBound);
   Reg#(TB) rb <- mkReg(minBound);
   Reg#(IA) ia <- mkReg(minBound);
   Reg#(IB) ib <- mkReg(minBound);

   Reg#(TF) fa <- mkReg(minBound);
   Reg#(TF) fb <- mkReg(minBound);


   function Stmt testSeqF ();
   return
   (seq
       for (ra <= minBound ; True; ra <= ra + epsilon )
          seq
             pfp(ra);
             $display("-->");
             for (rb <= minBound ; True; rb <= rb + epsilon )
                seq
                   if ((ra !=0) && (rb != 0)) seq
                   action
                      $write("          ");
                      pfp(rb) ; $write(":\t" );
                      FPQ1 q = fxptQuot(ra, rb);
                      pfp8(q); $write("  \t" );
                      FPQ2 rq = fxptQuot(rb, ra);
                      pfp8(rq);
                      // let prod = fxptMult(q,rq);
                      // if (prod != 1.0) begin
                      //    $write ("   >> ");
                      //    pfp(prod);
                      // end
                      $display("  ");
                   endaction
                   endseq
                   else
                      seq
                         noAction;
                      endseq
                   if (rb == maxBound) break;
                endseq

             $display ("-----------------");
             if (ra == maxBound) break;
          endseq
    endseq);
   endfunction

   function Stmt testSeqI ();
   return
   (seq
       $write ("      : ");
       for (ib <= minBound ; True; ib <= ib + 1 )
          seq
             action
                $write(" %6d ", ib);
             endaction
             if (ib == maxBound) break;
          endseq
       for (ia <= minBound ; True; ia <= ia + 1 )
          seq
             $write("\n%6d: ", ia);
             for (ib <= minBound ; True; ib <= ib + 1 )
                seq
		   if (ib == 0)
		      $write(" %6d ", 0);
		   else
                      $write(" %6d ", signedQuot(ia, ib));
                   if (ib == maxBound) break;
                endseq

             if (ia == maxBound) break;
          endseq
       $display ("\n-----------------");
    endseq);
   endfunction


   function Stmt testSeqDiv ();
   return
   (seq
       for (fa <= minBound ; True; fa <= fa + epsilon )
          seq
             pfp(fa); $display(": ");
             for (fb <= minBound ; True; fb <= fb + epsilon )
                seq
                   if (fa!=0 && fb!=0)
                   action
                      $write("          ");
                      pfp(fb) ; $write(":\t" );
                      let q = (fb ==0) ? 0 : fa/ fb;
                      pfp8(q); $write("  \t" );
                      let rq = (fa ==0) ? 0 :  fb/fa;
                      pfp8(rq);
                      // let prod = fxptMult(q,rq);
                      // if (prod != 1.0) begin
                      //    $write ("   >> ");
                      //    pfp(prod);
                      // end
                      $display("  ");
                   endaction
                   if (fb == maxBound) break;
                endseq

             if (fa == maxBound) break;
          endseq
       $display ("\n-----------------");
    endseq);
   endfunction


   mkAutoFSM
   (seq
       testSeqI;
       testSeqDiv;
       testSeqF;
    endseq);
endmodule
