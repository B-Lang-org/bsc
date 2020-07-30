// A better of example of BSV structures by showing how type
// parameterization and parmeterized functions  can be used.
// Also define operator overloading


// Define a structure for complex numbers
// Now using a type parameter, which can be (almost) any type
typedef struct {
        any_t  rel ;         // note that "real" is a keyword and cannot be used
        any_t  img ;
        } ComplexP#(type any_t) 
deriving ( Bits, Eq ) ;


// We need to define some type classes for Complex number,
   
// Types within the Literal class must define a fromInteger function,
// which we do here.
// This sets the imaginary part to 0 and the real part to the integer.
instance Literal#( ComplexP#(any_type) )      provisos( Literal#(any_type) );

   function fromInteger(n) ;
      return ComplexP{ rel: fromInteger(n), img: 0 } ;
   endfunction
endinstance


// Types within the Arith typeclass must have functions defined for +,
// -, negate and *.
instance Arith#( ComplexP#(any_type) ) 
      provisos( Arith#(any_type) ) ;

   function \+ (ComplexP#(any_type) in1, ComplexP#(any_type) in2 );
      return Complex{ rel: (in1.rel + in2.rel) ,
                      img: (in1.img + in2.img ) } ;
                            
   endfunction
   
   function \- (ComplexP#(any_type) in1, ComplexP#(any_type) in2 );
      return Complex{ rel: (in1.rel - in2.rel) ,
                      img: (in1.img - in2.img ) } ;
                            
   endfunction
   
   function \* (ComplexP#(any_type) in1, ComplexP#(any_type) in2 );
      any_type rr = in1.rel * in2.rel ;
      any_type ii = in1.img * in2.img ;
      any_type ir = in1.img * in2.rel ;
      any_type ri = in1.rel * in2.img ;
      
      return Complex{ rel: rr - ii,
                      img: ri + ir } ;
                            
   endfunction
   
   function negate ( ComplexP#(any_type) in1 );
      return 0 - in1 ;                            
   endfunction

endinstance

function Action printComplex( String msg, ComplexP#(any_type) cin )
   provisos( Bits#(any_type, sa ));
   action
      $display( "%s: R: %d I:%d", msg, cin.rel, cin.img ) ;
   endaction
endfunction

// The above lines should go into a separate library file.


typedef ComplexP#(Int#(32))  Complex ;
typedef ComplexP#(Int#(16))  Complex16 ;

// define a zero value complex number
Complex zeroComplex = Complex{ rel : 0, img : 0 } ;


(* synthesize *)
module sysComplex2 ();

   Reg#(Complex) c1 <- mkReg( 17 ) ;
   // Note that initialization can now be a literal
   
   Reg#(Complex) c2 <- mkReg( Complex{rel:1, img:2 } ) ;
   Reg#(Complex) c3 <- mkReg( zeroComplex ) ;

   Reg#(int) cnt <- mkReg(0) ;
   
   rule add_them ( True ) ;
      c3 <=  c1 + c2   ;      
   endrule

   rule mult_them_them2 ( True ) ;
      c2 <=  c1 * c2   ;
   endrule

   rule display ( True ) ;
      cnt <= cnt + 1 ;
      if ( cnt > 5 ) $finish(0) ;
      $display( "Values at cnt = %d", cnt );
      printComplex( "C1 is", c1 ) ;
      printComplex( "C2 is", c2 ) ;
//      printComplex( "C3 is", c3 ) ;
   endrule
        
endmodule
