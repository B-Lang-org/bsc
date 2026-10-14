
//@ \subsubsection{Complex}
//@ \index{Complex@\te{Complex} (package)|textbf}


//@ The \te{Complex} package provides a representation for complex
//@ numbers plus functions to operate on variables of this type.  The basic
//@ representation is the \te{Complex}
//@ structure, which is polymorphic on the type of data it holds.  For
//@ example, one can have complex numbers of type \te{Int} or of type
//@ \te{FixedPoint}.   A \te{Complex} number is represented in two
//@ part, the real part (rel) and the imaginary part (img).
//@ These fields are accessible though standard structure addressing,
//@ i.e., {\tt foo.rel and foo.img} where {\tt foo} is of type \te{Complex}.
//@
//@ # 5
typedef struct {
        any_t  rel ;
        any_t  img ;
        } Complex#(type any_t)
deriving ( Bits, Eq ) ;



//@ The \te{Arith} type class is defined for type \te{Complex}
//@ provide that \te{Arith} is defined for the specific type.
//@ Hence common infix operators (+, -, and *) and can be used to
//@ manipulate variables of type \te{Complex}.  Note however, that the
//@ complex multiplication (*) produces four multipliers in a
//@ combinational function; some other modules could
//@ accomplish the same function with less hardware and less
//@ throughput.
//@ # 2
instance Arith#( Complex#(any_type) )
      provisos( Arith#(any_type) ) ;

   function Complex#(any_type) \+ (Complex#(any_type) in1, Complex#(any_type) in2 );
      return Complex{ rel: (in1.rel + in2.rel) ,
                      img: (in1.img + in2.img ) } ;

   endfunction

   function Complex#(any_type) \- (Complex#(any_type) in1, Complex#(any_type) in2 );
      return Complex{ rel: (in1.rel - in2.rel) ,
                      img: (in1.img - in2.img ) } ;

   endfunction

   function Complex#(any_type) \* (Complex#(any_type) in1, Complex#(any_type) in2 );

      any_type rr = in1.rel * in2.rel ;
      any_type ii = in1.img * in2.img ;
      any_type ir = in1.img * in2.rel ;
      any_type ri = in1.rel * in2.img ;

      return Complex{ rel: rr - ii,
                       img: ri + ir } ;

   endfunction

   function Complex#(any_type) negate ( Complex#(any_type) in1 );
      return Complex{ rel: - in1.rel , img: - in1.img } ;
   endfunction

   function Complex#(any_type) \/ (Complex#(any_type) in1, Complex#(any_type) in2 );

      any_type d  = (in2.rel * in2.rel) + (in2.img * in2.img);
      any_type nr = (in1.rel * in2.rel) + (in1.img * in2.img);
      any_type ni = (in1.img * in2.rel) - (in1.rel * in2.img);

      return Complex { rel: nr/d,
                       img: ni/d };
   endfunction

   function \% (in1, in2);
      return error ("The operator " + quote("%") +
                    " is not defined for " + quote("Complex") + ".");
   endfunction

   // Rather than use the defaults for the following functions
   // (which would mention the full type in the error message)
   // we use special versions that omit the type parameter and
   // just say "Complex".

   function abs(x);
      return error ("The function " + quote("abs") +
                    " is not defined for " + quote("Complex") + ".");
   endfunction

   function signum(x);
      return error ("The function " + quote("signum") +
                    " is not defined for " + quote("Complex") + ".");
   endfunction

   function \** (x,y);
      return error ("The operator " + quote("**") +
                    " is not defined for " + quote("Complex") + ".");
   endfunction

   function exp_e(x);
      return error ("The function " + quote("exp_e") +
                    " is not defined for " + quote("Complex") + ".");
   endfunction

   function log(x);
      return error ("The function " + quote("log") +
                    " is not defined for " + quote("Complex") + ".");
   endfunction

   function logb(b,x);
      return error ("The function " + quote("logb") +
                    " is not defined for " + quote("Complex") + ".");
   endfunction

   function log2(x);
      return error ("The function " + quote("log2") +
                    " is not defined for " + quote("Complex") + ".");
   endfunction

   function log10(x);
      return error ("The function " + quote("log10") +
                    " is not defined for " + quote("Complex") + ".");
   endfunction

endinstance

instance SaturatingArith#(Complex#(any_type))
   provisos (SaturatingArith#(any_type));
   function Complex#(any_type) satPlus (SaturationMode mode, Complex#(any_type) x, Complex#(any_type) y);
      return cmplx(satPlus(mode, x.rel, y.rel), satPlus(mode, x.img, y.img));
   endfunction
   function Complex#(any_type) satMinus (SaturationMode mode, Complex#(any_type) x, Complex#(any_type) y);
      return cmplx(satMinus(mode, x.rel, y.rel), satMinus(mode, x.img, y.img));
   endfunction
endinstance

//@ The \te{Complex} type is a member of the \te{Literal} class, which
//@ defines a conversion from the compile-time \te{Integer} type to
//@ \te{Complex} type with the {\tt fromInteger} function.  This
//@ function converts the Integer to the real part, and sets the
//@ imaginary part to 0.
//@ # 2
instance Literal#( Complex#(any_type) )
   provisos( Literal#(any_type) );

   function fromInteger(n) ;
      return Complex{ rel: fromInteger(n), img: 0 } ;
   endfunction
   function inLiteralRange(a, i);
      return inLiteralRange(a.rel, i);
   endfunction
endinstance

//@ \index{cmplx@\te{cmplx} (complex function)|textbf}
//@ A simple constructor function is provided to set the fields.
//@ # 1
function Complex#(a_type) cmplx( a_type realA, a_type imagA ) ;
   return Complex{ rel: realA, img: imagA } ;
endfunction

//@ \index{cmplxMap@\te{cmplxMap} (complex function)|textbf}
//@ The {cmplxMap} function applies a function to each part of the
//@ complex structure.  This is useful for operations such as {\tt
//@ signExtend}, {\tt truncate}, etc.
//@ # 2
function Complex#(b_type) cmplxMap( function b_type mapFunc( a_type x),
                                    Complex#(a_type) cin ) ;
   return Complex{ rel: mapFunc( cin.rel ),
                   img: mapFunc( cin.img ) } ;
endfunction

//@ \index{cmplxSwap@\te{cmplxSwap} (complex function)|textbf}
//@ The {\tt cmplxSwap} function exchanges the real and imaginary
//@ parts.
//@ # 1
function Complex#(a_type) cmplxSwap( Complex#(a_type) cin ) ;
   return Complex{ rel: cin.img, img: cin.rel } ;
endfunction

//@ \index{cmplxConj@\te{cmplxConj} (complex function)|textbf}
//@ The {\tt cmplxConj} function conjugates (negates) the imaginary part.
//@ # 1
function Complex#(a_type) cmplxConj( Complex#(a_type) cin )
   provisos( Arith#(a_type) ) ;
   return Complex{ rel: cin.rel, img: - cin.img } ;
endfunction

// An instance of FShow is available provided t is a member of FShow as well.
instance FShow#(Complex#(t))
   provisos (FShow#(t));
   function Fmt fshow (Complex#(t) x);
      return $format("<C ", fshow(x.rel), ",", fshow(x.img), ">");
   endfunction
endinstance


//@ \index{cmplxWrite@\te{cmplxWrite} (complex function)|textbf}

//@ The {\tt cmplxWrite} function displays (via the \$write function)
//@ a complex number given a prefix string, an infix string, a
//@ postscript string, and an Action function which writes each part.
//@ {\tt cmplxWrite} is of type Action and can only be invoked in Action
//@ contexts such as Rules and Actions methods.
//@ # 3
function Action cmplxWrite( String pre, String infix, String post,
                            function Action writeaFunc( a_type x ),
                            Complex#(a_type) cin );
   action
   $write( "%s", pre );
   writeaFunc( cin.rel ) ;
   $write( "%s", infix ) ;
   writeaFunc( cin.img ) ;
   $write( "%s", post ) ;
   endaction
endfunction

//@ The following utility function is provided for writing data
//@ in decimal format. An example of its use is show below.
//@ # 3
function Action writeInt( Int#(n) ain ) ;
   $write( "%0d", ain ) ;
endfunction

//@ For example, the following code displays the a complex number
//@ as ``{\tt( -2 + 7i )}''.
//@ \begin{libverbatim}
//@  Complex#(Int#(6)) c = cmplx(-2,7) ;
//@  cmplxWrite( "( ", " + ", "i)", writeInt, c );
//@ // Note that writeInt is passed as an argument to the cmplxWrite function.
//@ \end{libverbatim}


// Lets define a function to printComplex numbers.
function Action printComplex( String msg, Complex#(any_type) cin )
   provisos( Bits#(any_type, pa ));
   action
      $display( "%Br: %d I:%d", msg, cin.rel, cin.img ) ;
   endaction
endfunction
