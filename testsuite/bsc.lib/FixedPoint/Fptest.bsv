
import FixedPoint :: * ;


// Extended precision multiplication
// Output must be at least as big the larger input size
function FixedPoint#(ri,rf)  fxptMult2 (
                                       FixedPoint#(ai,af) a,
                                       FixedPoint#(bi,bf) b )
   provisos(
            Add#(ai,bi,pi)
            ,Add#(af,bf,pf)
            ,Add#(xxA,ri,pi)
            ,Add#(xxB,rf,pf)
            ,Add#(pi,pf,pb)
            ,Add#(ai,af,ab)
            ,Add#(bi,bf,bb)
            ,Add#(ab,bb,pb)
            ,Min#(ai, 1, 1)
            ,Min#(bi, 1, 1)
            ,Min#(ri, 1, 1)
            ) ;

   FixedPoint#(pi,pf) prod = fxptMult( a, b ) ;
   return fxptTruncate( prod ) ;

endfunction


// A print utility for debug
function Action printFixedPoint( String msg, Integer fwidth, FixedPoint#(i,f) a )
   provisos (
             Add#(i, f, TAdd#(i,f)),
             Add#(1, xxxA, i )
             ) ;
   action
      $write( "%s(%b.%b) ", msg, fxptGetInt(a), fxptGetFrac(a) );
      fxptWrite( fwidth, a ) ;
      $display("") ;
   endaction
endfunction

(* noinline *)
function FixedPoint#(1,15) testAdd115( FixedPoint#(1,15) a, FixedPoint#(1,15) b ) ;
   return  a + b  ;
endfunction

(* noinline *)
function FixedPoint#(2,15) testMult15( FixedPoint#(1,7) a, FixedPoint#(1,8) b ) ;
   return  fxptMult(a,b)  ;
endfunction

(* noinline *)
function FixedPoint#(2,13) testMult213( FixedPoint#(1,7) a, FixedPoint#(1,8) b ) ;
   return  fxptMult2(a,b)  ;     // use truncated result
endfunction

(* noinline *)
function FixedPoint#(3,13) testshift213( FixedPoint#(3,13) a, Nat  b ) ;
   return  a >> b ;
endfunction


typedef FixedPoint#(6,3)  TFXPT ;
(* synthesize *)
module sysFptest( );

   let half = fromRational( 1, 2) ;
   let  quarter = half * half ;
   Reg#(TFXPT) r0 <- mkReg(0) ;
   Reg#(TFXPT) r1 <- mkReg(1) ;
   Reg#(TFXPT) r2 <- mkReg(2) ;
   Reg#(TFXPT) r3 <- mkReg(2) ;

   Reg#(int) cnt <- mkReg(0) ;

   let pfp = printFixedPoint ;  // rename a function to save typing !

   rule test (True) ;
      TFXPT sum = r1 + r2 ;
      TFXPT prod = r1 * r2 ;
      FixedPoint#(8,4) prod2 = fxptMult2( r1, r2 ) ;
      FixedPoint#(12,6) prodF = fxptMult( r1, r3 ) ;

      $display( "r1: %b  r2: %b,   sum: %b   prod: %b prod2: %b, prodF: %b",
               r1, r2, sum, prod, prod2, prodF ) ;
      pfp( "r1: ",5, r1 ) ;
      pfp( "r2: ",5, r2 ) ;
      pfp( "sum: ",5, sum ) ;
      pfp( "prod:     ",5, prod ) ;
      pfp( "prod2:  ",5, prod2 ) ;
      pfp( "prodF: ",5, prodF ) ;

      r1 <= r1 + (half*quarter) ;
      r2 <= r2 + (half * half) ;
      r3 <= r3 + (half*half) ;
      cnt <= cnt + 1 ;
      if ( cnt > 40 ) $finish(0) ;
   endrule

   Reg#(Bool)  doOnce <- mkReg(True) ;

   rule once (doOnce);
      doOnce <= False ;
      FixedPoint#(4,4) eps = epsilon ;
      FixedPoint#(4,4) mnb = minBound ;
      FixedPoint#(4,4) mxb = maxBound ;
      FixedPoint#(4,4) temp = 0 ;
      FixedPoint#(4,4) one = 1 ;
      FixedPoint#(4,4) halfv = 1 >> 1  ;

      pfp( "zero: ", 5, temp ) ;
      pfp( "one:  ", 5, one ) ;
      pfp( "half: ", 5, halfv ) ;
      pfp( "epsilon: ", 5, eps ) ;
      pfp( "minBound: ", 5, mnb ) ;
      pfp( "maxBound: ", 5, mxb ) ;

      temp = temp - 1 ;
      pfp( "0 - 1 ", 5, temp ) ;

      temp = temp + half ;
      pfp( "0 - 1 + half -(1/2) ", 5, temp ) ;

      temp = temp >> 1 ;
      pfp( "-0.25 ", 5, temp ) ;
      temp = temp >> 1 ;
      pfp( "-0.25/2 ", 5, temp ) ;
      temp = temp >> 1 ;
      pfp( "-0.25/4 ", 5, temp ) ;
      temp = temp >> 1 ;
      pfp( "-0.25/8 ", 5, temp ) ;

      temp = minBound + eps ;
      pfp( "minBound + epi", 5, temp ) ;

      temp = maxBound - eps ;
      pfp( "maxBound - epi", 5, temp ) ;

      temp = minBound + maxBound ;
      pfp( "sum of min and max bounds: ", 5, temp ) ;


      temp = eps << 1 ;
      pfp( "2 * eps  ", 5, temp ) ;
      temp = temp << 1 ;
      pfp( "4 * eps  ", 5, temp ) ;
      temp = temp << 1 ;
      pfp( "8 * eps  ", 5, temp ) ;
      temp = temp << 1 ;
      pfp( "16 * eps ", 5, temp ) ;
      temp = temp << 1 ;
      pfp( "32 * eps ", 5, temp ) ;
      temp = temp << 1 ;
      pfp( "64 * eps ", 5, temp ) ;
      temp = temp << 1 ;
      pfp( "128 * eps", 5, temp ) ;
      temp = temp << 1 ;
      pfp( "256 * eps", 5, temp ) ;

      temp = minBound + (epsilon << 1) ;
      pfp( "full ", 5, temp ) ;
      pfp( "4    ", 4, temp ) ;
      pfp( "3    ", 3, temp ) ;
      pfp( "2    ", 2, temp ) ;
      pfp( "1    ", 1, temp ) ;
      pfp( "0    ", 0, temp ) ;

      FixedPoint#(1,6) x = half + epsilon ;
      $write( "x is " ) ; fxptWrite( 7, x ) ; $display("" ) ;

      // From Rational tests.
      FixedPoint#(1,6) r6 = fromRational( 1,3) ;
      pfp( "1/3 is ", 7, r6 ) ;

      FixedPoint#(1,8) r8 = fromRational( 1,3) ;
      pfp( "1/3 is ", 7, r8 ) ;

      FixedPoint#(1,10) r10 = fromRational( 1,3) ;
      pfp( "1/3 is ", 7, r10 ) ;

      FixedPoint#(3,16) r16 = fromRational( 1,3) ;
      pfp( "1/3 is ", 7, r16 ) ;

      r16 = fromRational( 31415926, 10000000) ;
      pfp( "pi  is ", 7, r16 ) ;

      r16 = fromRational( 4, -1)  ;
      pfp( "-4     ", 7, r16 ) ;

      r16 = fromRational( -3999999, -1000000)  ;
      pfp( "a bruised 4 is ", 7, r16 ) ;
   endrule

endmodule
