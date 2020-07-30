
import Complex :: * ;
import FixedPoint :: * ;

// A more complex example showing how to define Complex number
// containing fixed point


// Define type synonym for easier typing

// Our basic fixed point type
typedef FixedPoint#(1,4)      FPType ;

// Our complex type
typedef Complex#(FPType)     ComplexD ;


// Some constants  of FPType
FPType fhalf    = fromRational(1, 2 ) ;
FPType fquarter = fromRational(1, 4 ) ;




(* synthesize *)
module sysCmplxTest ();

   Reg#(ComplexD) c1 <- mkReg( cmplx(fquarter,fhalf) ) ;

   Reg#(ComplexD) c2 <- mkReg( cmplx(fhalf, fquarter) ) ;
   Reg#(ComplexD) c3 <- mkReg( 0 ) ;

   Reg#(int) cnt <- mkReg(0) ;

   rule add_them ( True ) ;
      c3 <=  c1 + c2   ;
   endrule

   rule mult_them_them2 ( True ) ;
      c2 <=  c1 * c2   ;
   endrule

   function Action writeh ( a x ) provisos( Bits#(a,sa) ) ;
      $write( "0x%0h", x ) ;
   endfunction

   rule first ( cnt == 0 );
      Complex#(Int#(6)) c = cmplx(-2,7) ;   
      cmplxWrite( "( ", " + ", "i)", writeInt, c ); $display("") ;
      
      // Some tests for swap and map
      Complex#(Int#(4)) foo = cmplx( 2, -7 ) ;
      cmplxWrite( "foo is: ( ", " + ", "i)", writeh, foo ) ; $display("" ) ;

      foo = cmplxSwap( foo ) ;
      cmplxWrite( "swapfoo is: ( ", " + ", "i)", writeInt, foo ) ; $display("" ) ;

      Complex#(FixedPoint#(4,8)) fpfoo = cmplxMap( fromInt, foo ) ;
      cmplxWrite( "fpfoo is: ( ", " + ", "i)", fxptWrite(4), fpfoo ) ; $display("" ) ;

      function a rshiftx( Nat n, a op) provisos( Bitwise#(a) );
         return op >> n ;
      endfunction

      fpfoo = cmplxMap( rshiftx(4), fpfoo ) ;
      cmplxWrite( "fpfoo is: ( ", " + ", "i)", fxptWrite(4), fpfoo ) ; $display("" ) ;
   endrule

   
   rule display ( True ) ;
      cnt <= cnt + 1 ;
      if ( cnt > 5 ) $finish(0) ;
      $display( "Values at cnt = %d", cnt );
      cmplxWrite( "C1 is: ( ", " + ", "i)", fxptWrite(4), c1 ) ; $display("" ) ;
      cmplxWrite( "C2 is: ( ", " + ", "i)", fxptWrite(4), c2 ) ; $display("" ) ;
      cmplxWrite( "C3 is: ( ", " + ", "i)", fxptWrite(4), c3 ) ; $display("" ) ;

   endrule

endmodule
