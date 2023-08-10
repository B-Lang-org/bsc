import FixedPoint::*;
import StmtFSM::*;

// Test types
typedef FixedPoint#(2,2)  TA;
typedef FixedPoint#(2,2)  TB;

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
module sysExtendedPrecision();

   let pfp = printFixedPoint("",4) ;  // rename a function to save typing !
   let pfp8 = printFixedPoint("",8) ;  // rename a function to save typing !

   Reg#(TA) ra <- mkReg(minBound);
   Reg#(TB) rb <- mkReg(minBound);

   function Stmt testSeq ();
   return
   (seq
       for (ra <= minBound ; True; ra <= ra + epsilon )
          seq
             pfp(ra);
             $display("-->");
             for (rb <= minBound ; True; rb <= rb + epsilon )
                seq
                   action
                      $write("          ");
                      pfp(rb) ; $write(":\t" );
                      let x = fxptAdd(ra, rb);
                      pfp(x); $write("\t" );
                      let d = fxptSub(ra, rb);
                      pfp(d);$write("\t" );
                      $display("  ");
                   endaction
                   if (rb == maxBound) break;
                endseq

             $display ("-----------------");
             if (ra == maxBound) break;
          endseq
    endseq);
   endfunction

   mkAutoFSM(testSeq);
endmodule
