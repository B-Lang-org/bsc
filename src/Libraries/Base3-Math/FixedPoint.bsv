
import Real :: *;

//@ \subsubsection{FixedPoint}
//@ \index{FixedPoint@\te{FixedPoint} (package)|textbf}
//@
//@ The \te{FixedPoint} library package defines a type for
//@ representing fixed-point numbers and corresponding functions to
//@ operate and manipulate variables of this type.
//@
//@ A fixed-point number represents signed real numbers which
//@ have a fixed number of binary digits (bits) before and after the binary
//@ point. The type constructor for Fixed point number takes two
//@ numeric types as argument, the first (isize) defines the number of bits
//@ to the left of the binary point (the integer part), while the
//@ second (fsize)
//@ defines the number of bits to the right of the binary point, the
//@ fractional part.
//@
//@  The following data structure defines this type, while some
//@ utility functions provide the reading of the integer and
//@ fractional parts.
//@ # 5
typedef struct {
                Bit#(isize) i;
                Bit#(fsize) f;
                }
FixedPoint#(numeric type isize, numeric type fsize )
deriving( Eq ) ;


function FixedPoint#(i,f)  _fromInternal ( Int#(b) x )
   provisos ( Add#(i,f,b) );
   return unpack ( pack (x) );
endfunction

function  Int#(b) _toInternal ( FixedPoint#(i,f) x )
   provisos ( Add#(i,f,b) );
   return unpack ( pack (x) );
endfunction

instance Bits#( FixedPoint#(i,f), b )
   provisos ( Add#(i,f,b) );

   function Bit#(b) pack (FixedPoint#(i,f) x);
      return { pack(x.i),pack(x.f) };
   endfunction
   function FixedPoint#(i,f) unpack ( Bit#(b) x );
      match {.i,.f} = split (x);
      return FixedPoint { i:i, f:f } ;
   endfunction
endinstance


//@ \index{fxptGetInt@\te{fxptGetInt} (fixed-point function)|textbf}
//@ Utility functions are provided to extract the integer and
//@ fractional parts.
//@ # 3
function Int#(isize) fxptGetInt ( FixedPoint#(isize, fsize) a );
   return unpack (a.i);
endfunction

//@ \index{fxptGetFrac@\te{fxptGetFrac} (fixed-point function)|textbf}
//@ # 2
function UInt#(fsize) fxptGetFrac ( FixedPoint#(isize, fsize) a );
   return unpack (a.f);
endfunction


//@
//@ The range of values, $v$, representable with a signed
//@ fixed-point number of type \te{FixedPoint\#(isize, fsize)} is
//@ $+(2^{isize -1} - 2^{-fsize}) \leq v \leq -2^{isize - 1}$.
//@ This range is provided by the members of
//@  \te{Bounded} type class to which \te{FixedPoint} belongs. The
//@ function {\tt epsilon} returns the smallest representable quantum
//@ by a specific type, $2^{-fsize}$.
//@ For example, a variable $v$ of type \te{FixedPoint\#(2,3)} type can
//@ represent numbers from 3.875 ($3\frac{7}{8}$) to $-4.0$ in
//@ intervals of $\frac{1}{8} = 0.125$. The type
//@ \te{FixedPoint\#(5,0)} is equivalent to \te{Int\#(5)}.
//@ # 1
instance Bounded#( FixedPoint#(i,f) )
   provisos( Add#(i,f,b) );

   function  FixedPoint#(i,f) minBound() ;
      Int#(b)  minb = minBound ;
      return _fromInternal (minb) ;
   endfunction

   function  FixedPoint#(i,f) maxBound() ;
      Int#(b)  maxb = maxBound ;
      return _fromInternal (maxb);
   endfunction
endinstance


instance RealLiteral#( FixedPoint# (i, f) )
   provisos ( Min#(i,1,1) );

function FixedPoint#(i,f) fromReal ( Real n )
   provisos (
             Add#(i,f,fpsize)
             ,Add#(54,fpsize,workingSize)
	     ,Min#(i,1,1)
             );

   let {s,m,e} =  ( decodeReal (n) ) ;
   Int#(workingSize) joined = fromInteger(m);
   Int#(12) be = fromInteger(e);

   Int#(fpsize) bres = ? ;
   Bool overflow = ? ;
   let ediff = e+valueOf(f) ;
   if (ediff < 0)
      begin
         // Shifting to 0 results in 0, this is ok
         // Round toward 0 for negative numbers
         Int#(workingSize) round = s ? 0 : ('b1 << ((0-ediff)-1));
         Int#(workingSize) aligned = (joined + round) >> (0- ediff) ;
         bres = truncate (aligned);
         // Possible overflow on truncate
         overflow = ( signExtend(bres) != aligned );
      end
   else
      begin
         // overflow if data is shifted off left end
         // or shifted to 0
         Int#(workingSize) aligned = joined << ediff ;
         bres = truncate (aligned);
         overflow =  ( signExtend(bres) != aligned ) || (bres == 0 && joined != 0 ) ;
      end

   String bmsg = s ? "maxBound" : "minBound" ;
   String msg = ("Converting from RealLiteral '" +
                 realToString (n) +
                 "' to type 'FixedPoint#(" + integerToString(valueOf(i)) +
                 "," + integerToString(valueOf(f)) +
                 ")' exceeds the FixedPoint range, replacing with " + bmsg + "."
                 ) ;
   FixedPoint#(i,f) res1 = _fromInternal ( bres ) ;
   FixedPoint#(i,f) bound = s ? maxBound : minBound ;
   FixedPoint#(i,f) res = overflow ? warning (msg, bound) : res1 ;
   return res ;

endfunction
endinstance


//@ \index{epsilon@\te{epsilon} (fixed-point function)|textbf}
//@ # 1
function FixedPoint#(i,f) epsilon ()
   provisos(
	    Min#(i,1,1),
	    Min#(TAdd#(i,f),2,2)
	    );

      Int#(b)  eps = 'b01  ;
      return _fromInternal (eps);
endfunction


//@ The type \te{FixedPoint} belongs to the \te{Arith} type class,
//@ hence the common infix operators (+, -, and *) and can be used to
//@ manipulate variables of type \te{FixedPoint}.
//@ # 3
instance Arith#( FixedPoint#(i,f) )
   provisos( Add#(i,f,b)
            ,Add#(TAdd#(i,i), TAdd#(f,f), TAdd#(b,b))
	    ,Min#(i,1,1)
	    ,Min#(TAdd#(i, f), 2, 2)
            );

   // Addition does not change the binary point
   function FixedPoint#(i,f) \+ (FixedPoint#(i,f) in1, FixedPoint#(i,f) in2 );
       return _fromInternal ( _toInternal (in1) + _toInternal (in2) ) ;
   endfunction

   // Similar subtraction does not as well
   function FixedPoint#(i,f) \- (FixedPoint#(i,f) in1, FixedPoint#(i,f) in2 );
       return _fromInternal ( _toInternal (in1) - _toInternal (in2) ) ;
   endfunction

   // For multiplication, the computation is accomplished in full
   // precision, and the result truncated to fit
   function FixedPoint#(i,f) \* (FixedPoint#(i,f) in1, FixedPoint#(i,f) in2 );

      FixedPoint#(TAdd#(i,i), TAdd#(f,f)) prod = fxptMult(in1, in2);
      return  fxptTruncateRoundSat(Rnd_Zero, Sat_Bound, prod);
   endfunction

   // negate is defined in terms of the subtraction operator.
   function FixedPoint#(i,f) negate (FixedPoint#(i,f) in1 );
      return _fromInternal ( 0 - _toInternal(in1) );
   endfunction

   // quotient used full precision and then truncates
   function FixedPoint#(i,f) \/ (FixedPoint#(i,f) in1, FixedPoint#(i,f) in2);
      FixedPoint#(TAdd#(TAdd#(1,i),f), TAdd#(2,f)) q = fxptQuot (in1, in2);
      return fxptTruncateRoundSat(Rnd_Zero, Sat_Bound, q);
   endfunction

   // remainder is not defined for FixedPoint
   function FixedPoint#(i,f) \% (FixedPoint#(i,f) in1, FixedPoint#(i,f) in2);
      return error ("The operator " + quote("%") +
                    " is not defined for " + quote("FixedPoint") + ".");
   endfunction

   function FixedPoint#(i,f) abs( FixedPoint#(i,f) x);
      // to prevent the instance from being recursive,
      // we don't use "-" ("negate") directly on "x"
      FixedPoint#(i,f) neg_x = _fromInternal( 0 - _toInternal(x) ) ;
      Int#(b) t = _toInternal(x);
      return ( (t < 0) ? neg_x : x );
   endfunction

   function FixedPoint#(i,f) signum( FixedPoint#(i,f) x);
      Int#(i) t = unpack(x.i);
      Int#(i) r = signum(t);
      return FixedPoint { i: pack(r), f:0 } ;
   endfunction

   // Rather than use the defaults for the following functions
   // (which would mention the full type in the error message)
   // we use special versions that omit the type parameter and
   // just say "FixedPoint".

   function \** (x,y);
      return error ("The operator " + quote("**") +
                    " is not defined for " + quote("FixedPoint") + ".");
   endfunction

   function exp_e(x);
      return error ("The function " + quote("exp_e") +
                    " is not defined for " + quote("FixedPoint") + ".");
   endfunction

   function log(x);
      return error ("The function " + quote("log") +
                    " is not defined for " + quote("FixedPoint") + ".");
   endfunction

   function logb(b,x);
      return error ("The function " + quote("logb") +
                    " is not defined for " + quote("FixedPoint") + ".");
   endfunction

   function log2(x);
      return error ("The function " + quote("log2") +
                    " is not defined for " + quote("FixedPoint") + ".");
   endfunction

   function log10(x);
      return error ("The function " + quote("log10") +
                    " is not defined for " + quote("FixedPoint") + ".");
   endfunction

endinstance


instance SaturatingArith#(FixedPoint#(i,f));
   function FixedPoint#(i,f) satPlus (SaturationMode smode, FixedPoint#(i,f) x, FixedPoint#(i,f) y);
      return _fromInternal( satPlus (smode, _toInternal(x), _toInternal(y)) );
   endfunction
   function FixedPoint#(i,f) satMinus (SaturationMode smode, FixedPoint#(i,f) x, FixedPoint#(i,f) y);
      return _fromInternal( satMinus (smode, _toInternal(x), _toInternal(y)) );
   endfunction
endinstance

//@ The type \te{FixedPoint} belongs to the \te{Literal} type class,
//@ which allows conversion from (compile-time) type \te{Integer} to type
//@ \te{FixedPoint}.  Note that only the integer part is assigned.
//@ # 3
instance Literal#( FixedPoint#(i,f) )
   provisos( Add#(i,f,b),
	     Min#(i,1,1) );

   // A way to convert Integer constants to fixed points
   function FixedPoint#(i,f) fromInteger( Integer n) ;

      // Convert to explicit types to all for bounds checking
      Int#(i) conv = fromInteger(n) ;
      return FixedPoint {i:pack(conv),
                         f:0 };
   endfunction
   function inLiteralRange(f,n);
      Int#(i) int_part = ?;
      return(inLiteralRange(int_part,n));
   endfunction
endinstance




//@ \index{fromInt@\te{fromInt} (fixed-point function)|textbf}
//@ \index{fromUInt@\te{fromUInt} (fixed-point function)|textbf}
//@ To convert run-time \te{Int} and \te{UInt} values to type
//@ \te{FixedPoint}, the following conversion functions are
//@ provided. Both of these functions invoke the necessary extension
//@ of the source operand.
//@ # 5
function FixedPoint#(ir,fr) fromInt( Int#(ia) inta )
   provisos ( Add#(ia, xxA, ir ),         // ir >= ia
	      Min#(ir, 1, 1)
             ) ;

   Int#(ir)  temp = signExtend( inta ) ;
   return FixedPoint { i:pack(temp), f:0 } ;
endfunction


//@ # 5
function FixedPoint#(ir,fr) fromUInt( UInt#(ia) uinta )
   provisos ( Add#(ia,  1, ia1),          // ia1 = ia + 1
              Add#(ia1,xxB, ir ),         // ir >= ia1
	      Min#(ir, 1, 1)
             );
   Bit#(ia1) t1 = {1'b0, pack(uinta) };
   Bit#(ir)  temp = zeroExtend( t1 ) ;
   return FixedPoint { i:temp, f:0 } ;
endfunction


//@ Non-integer compile time constants may be specified by a rational
//@ number which is a ratio of two integers.  For example, one-third
//@ may be specified by {\tt fromRational(1,3);}, while {$\pi$} can be
//@ specified as {\tt fromRational( 31415926, 10000000); }.
//@ #  2
function FixedPoint#(i,f) fromRational( Integer numerator, Integer denominator)
   provisos ( //Add#(1, xxA, i )          // i >= 1
             Add#(i,f,b),
	     Min#(i,1,1) );
   let zmsg = error( "FixedPoint::fromRational " +
                    "denominator cannot be zero." );

   let rmsg = error( "FixedPoint::fromRational " +
                     "The rational number: " +
                     fromInteger( numerator ) + " / " +
                     fromInteger (denominator) +
                    " cannot be represented in a FixedPoint#(" +
                    fromInteger( valueOf(i) ) + "," +
                    fromInteger( valueOf(f) ) + ")."
                    );

   Integer temp = numerator * (2 ** valueOf(f)) ;
   temp = (denominator != 0) ?  div( temp, denominator ) : zmsg ;

   Integer max = 2 ** (valueOf(i) + valueOf(f) - 1) ;
   Bool rangeOk = (temp < max) && (temp >= negate( max ) ) ;

   Int#(b) res = rangeOk ? fromInteger( temp ) : rmsg ;
   return _fromInternal(res);

endfunction


//@ \index{fxptMult@\te{fxptMult} (fixed-point function)|textbf}
//@ At times, a full precision multiplication may be required, where
//@ the result is sum of the field sizes of the operands.  Note that
//@ the operand do not have to be the same type (sizes), as is
//@ required for the infix multiplication (*) operator.
//@ # 5
function FixedPoint#(ri,rf)  fxptMult( FixedPoint#(ai,af) a,
                                       FixedPoint#(bi,bf) b  )
   provisos (Add#(ai,bi,ri)   // ri = ai + bi
             ,Add#(af,bf,rf)   // rf = af + bf
             ,Add#(ai,af,ab)
             ,Add#(bi,bf,bb)
             ,Add#(ab,bb,rb)
             ,Add#(ri,rf,rb)
	     ,Min#(ai,1,1)
	     ,Min#(bi,1,1)
	     ,Min#(ri,1,1)
            ) ;

   Int#(ab) ap = _toInternal(a);
   Int#(bb) bp = _toInternal(b);

   Int#(rb) prod = signedMul(ap, bp); // signed integer multiplication

   return _fromInternal(prod);

endfunction

// Full precision, no bits are dropped
function FixedPoint#(ri,rf)  fxptAdd( FixedPoint#(ai,af) a,
                                       FixedPoint#(bi,bf) b  )
   provisos (Max#(ai,bi,rim)   // ri = 1 + max(ai, bi)
             ,Add#(1,rim, ri)
             ,Max#(af,bf,rf)   // rf = max (af, bf)
             ,Add#(_x1,ai, ri) // teach bsc math
             ,Add#(_x2,bi, ri)
             ,Add#(_x3,af,rf)
             ,Add#(_x4,bf,rf)
	     ,Min#(ai,1,1)
	     ,Min#(bi,1,1)
	     ,Min#(ri,1,1)
             ) ;
   return fxptSignExtend(a) + fxptSignExtend(b);
endfunction

function FixedPoint#(ri,rf)  fxptSub( FixedPoint#(ai,af) a,
                                     FixedPoint#(bi,bf) b  )
   provisos (Max#(ai,bi,rim)   // ri = 1 + max(ai, bi)
             ,Add#(1,rim, ri)
             ,Max#(af,bf,rf)   // rf = max (af, bf)
             ,Add#(_x1,ai, ri) // teach bsc math
             ,Add#(_x2,bi, ri)
             ,Add#(_x3,af,rf)
             ,Add#(_x4,bf,rf)
	     ,Min#(ai,1,1)
	     ,Min#(bi,1,1)
	     ,Min#(ri,1,1)
             ) ;
   return fxptSignExtend(a) - fxptSignExtend(b);
endfunction


function FixedPoint#(ri,rf)  fxptQuot (FixedPoint#(ai,af) a,
                                       FixedPoint#(bi,bf) b  )
   provisos (Add#(ai1,bf,ri)      // ri = ai + bf + 1
             ,Add#(ai,1,ai1)
             ,Add#(af,_xf,rf)     // rf >= af
             ,Add#(ri, rf, TAdd#(ai1, TAdd#(TAdd#(af, af), _xf)))
	     ,Min#(ai,1,1)
	     ,Min#(bi,1,1)
	     ,Min#(ri,1,1)
             ) ;

   FixedPoint#(ai1, TAdd#(af,af)) ax1 = fxptSignExtend(a);
   FixedPoint#(ai1, TAdd#(TAdd#(af,af), _xf)) ax2 = fxptSignExtend(ax1);
   return _fromInternal( signedQuot (_toInternal(ax2), _toInternal(b) ));

endfunction


// A saturating Fixed Point truncation
// If the value cannot be represented in its truncated form minBound or maxBound is returned.
function FixedPoint#(ri,rf) fxptTruncateSat (SaturationMode smode, FixedPoint#(ai,af) din)
   provisos (Add#(ri,idrop,ai)
             ,Add#(rf,_f,af)
	     ,Min#(ai,1,1)
	     ,Min#(ri,1,1)
	     ,Min#(TAdd#(ri, rf), 2, 2)
             );

   FixedPoint#(ri,rf) res = fxptTruncate(din);

   Bit#(1) dinSign    = msb(din);
   Bit#(1) resSign    = msb(res);
   Bit#(idrop) check  = truncateLSB(din.i);
   Bool over          = dinSign == 0 && (resSign != 0 || check != 0);
   Bool under         = dinSign == 1 && (resSign != 1 || ~check != '0);
   Bool isMin         = res == minBound;
   case (smode)
      Sat_Wrap:        res = res;
      Sat_Bound:       res = over ? maxBound : (under ? minBound : res);
      Sat_Zero:        res = (over || under) ? 0 : res;
      Sat_Symmetric:   res = over? maxBound : ((under || isMin) ? (minBound + epsilon) : res);
   endcase

   return res;
endfunction

// Rounding modes
typedef enum {
              Rnd_Plus_Inf       // Round to Plus infinity SC_RND
              ,Rnd_Zero          // SC_RND_ZERO
              ,Rnd_Minus_Inf     // SC_RND_MIN_INF
              ,Rnd_Inf           // SC_RND_INF
              ,Rnd_Conv          // SC_RND_CONV
              ,Rnd_Truncate      // SC_TRN
              ,Rnd_Truncate_Zero // SC_TRN_ZERO
   } RoundMode
deriving (Bits, Eq);

function FixedPoint#(ri,rf) fxptTruncateRound (RoundMode rmode, FixedPoint#(ai,af) din)
   provisos (Add#(ri,idrop,ai)
             ,Add#(rf,fdrop,af)
             ,Min#(ai,1,1)
             ,Min#(ri,1,1)
	     ,Min#(TAdd#(ri, rf), 2, 2)
             );
   return fxptTruncateRoundSat(rmode, Sat_Wrap, din);
endfunction


function FixedPoint#(ri,rf) fxptTruncateRoundSat (RoundMode rmode, SaturationMode smode, FixedPoint#(ai,af) din)
   provisos (Add#(ri,idrop,ai)
             ,Add#(rf,fdrop,af)
             ,Min#(ai,1,1)
             ,Min#(ri,1,1)
	     ,Min#(TAdd#(ri, rf), 2, 2)
             );
   Bit#(n) msbMask = (~('b0)) >> 1; // 'b011111...

   FixedPoint#(ai,rf) res = fxptTruncate(din);

   Bit#(fdrop) x0  = truncate(din.f);
   Bool mD         = 1 == msb(x0) ;       // MSB of dropped bits
   Bool sR         = 1 == msb(din) ;      // sign of result
   Bool lR         = 1 == lsb(res) ;      // LSB of truncated result
   Bool r          = 0 != (x0 & msbMask); // dropped bit not including mD

   let rnd = case (rmode)
                 Rnd_Plus_Inf:      return mD;
                 Rnd_Zero:          return mD && (sR || r);
                 Rnd_Minus_Inf:     return mD && r;
                 Rnd_Inf:           return mD && (!sR || r);
                 Rnd_Conv:          return mD && (lR || r);
                 Rnd_Truncate:      return False;
                 Rnd_Truncate_Zero: return sR && (mD || r);
              endcase;
   res = satPlus(smode, res, rnd ? epsilon : 0);
   FixedPoint#(ri,rf) sat = fxptTruncateSat(smode, res);
   return sat;
endfunction



//@ \index{fxptTruncate@\te{fxptTruncate} (fixed-point function)|textbf}
//@ {\tt fxptTruncate} is a general truncate function which converts
//@ variables to
//@ \te{FixedPoint\#(ai,af)} to type \te{FixedPoint\#(ri,rf)}, where
//@ $ai \geq ri$ and $af \geq rf$.  This function truncates bit as
//@ appropriate from the most significant integer bits and the least
//@ significant fractional bits.
//# 5
function FixedPoint#(ri,rf) fxptTruncate( FixedPoint#(ai,af) a )
   provisos( Add#(xxA,ri,ai),    // ai >= ri
             Add#(xxB,rf,af),    // af >= rf
             Min#(ai,1,1),
             Min#(ri,1,1)
            ) ;

   FixedPoint#(ri,rf) res = FixedPoint {i: truncate (a.i),
                                        f: truncateLSB (a.f) } ;
   return res;

endfunction


//@ \index{fxptSignExtend@\te{fxptSignExtend} (fixed-point function)|textbf}
//@ \index{fxptZeroExtend@\te{fxptZeroExtend} (fixed-point function)|textbf}
//@ {\tt fxptSignExtend} is a general sign extend function which
//@ converts variables of type
//@ \te{FixedPoint\#(ai,af)} to type \te{FixedPoint\#(ri,rf)}, where
//@ $ai \leq ri$ and $af \leq rf$.  The integer part is sign extended,
//@ while additional 0 bits are added to least significant end of the
//@ fractional part.
//# 5
function FixedPoint#(ri,rf) fxptSignExtend( FixedPoint#(ai,af) a )
   provisos( Add#(xxA,ai,ri),      // ri >= ai
             Add#(fdiff,af,rf),    // rf >= af
             Min#(ai,1,1),
             Min#(ri,1,1)
            )  ;
   return FixedPoint {i:signExtend(a.i),
                      f:{a.f,0} } ;
endfunction


//@ A general zero extend function is also provided.
//@ # 5
function FixedPoint#(ri,rf) fxptZeroExtend( FixedPoint#(ai,af) a )
   provisos( Add#(xxA,ai,ri),    // ri >= ai
             Add#(xxB,af,rf),    // rf >= af
             Min#(ai,1,1),
             Min#(ri,1,1)
            ) ;
   return FixedPoint {i: zeroExtend (a.i),
                      f: {a.f,0} };
endfunction


//@ In addition to equality and inequality comparisons,
//@ \te{FixedPoint} variables can be compared by the relational
//@ operators provided by the \te{Ord} type class. i.e., <, >, <=, and
//@ >=.
//@ # 2
instance Ord#( FixedPoint#(i,f) )
   provisos( Add#(i,f,b),
             Min#(i,1,1) );

   function Bool \< (FixedPoint#(i,f) in1, FixedPoint#(i,f) in2 ) ;
      Int#(b) n1 = _toInternal(in1) ;
      Int#(b) n2 = _toInternal(in2) ;
      return n1 < n2 ;
   endfunction

   function Bool \<= (FixedPoint#(i,f) in1, FixedPoint#(i,f) in2 );
      Int#(b) n1 = _toInternal(in1) ;
      Int#(b) n2 = _toInternal(in2) ;
      return n1 <= n2;
   endfunction

   function Bool \> (FixedPoint#(i,f) in1, FixedPoint#(i,f) in2 );
      Int#(b) n1 = _toInternal(in1) ;
      Int#(b) n2 = _toInternal(in2) ;
      return n1 > n2 ;
   endfunction

   function Bool \>= (FixedPoint#(i,f) in1, FixedPoint#(i,f) in2 );
      Int#(b) n1 = _toInternal(in1) ;
      Int#(b) n2 = _toInternal(in2) ;
      return n1 >= n2 ;
   endfunction

endinstance


//@ Left and right shifts are provided for \te{FixedPoint} variables
//@ as part of the \te{Bitwise} type class.  Note that the shift right
//@ ({\verb^>>^}) function does an arithmetic shift, thus preserving the sign
//@ of the operand. Note that a right shift of 1 is equivalent to a
//@ division by 2, except when the operand is equal to $- {\tt
//@ epsilon}$.  The other
//@ methods of \te{Bitwise} type class are not provided since they
//@ have no operational meaning on \te{FixedPoint} variables.
//@ # 2
instance Bitwise#( FixedPoint#(i,f) )
   provisos (Add#(i,f,b),
             Min#(i,1,1)
           );

   function FixedPoint#(i,f) \>> (FixedPoint#(i,f) in1, ix sftamt )
      provisos(PrimShiftIndex#(ix, dx));
      Int#(b) bitsin = _toInternal(in1) ;
      return _fromInternal ( bitsin >> sftamt );
   endfunction

   function FixedPoint#(i,f) \<< (FixedPoint#(i,f) in1, ix sftamt )
      provisos(PrimShiftIndex#(ix, dx));
      Int#(b) ini = _toInternal(in1);
      return _fromInternal ( ini << sftamt );
   endfunction

   // We do not provide the following since their operation are
   // meaningless w.r.t. FixedPoint variables
   function invert (in1);
      return error ("The invert operator is not defined for " +
                    quote ("FixedPoint") + ".");
   endfunction
   function \^~ (in1, in2);
      return error ("The operator " + quote("^~") +
                    " is not defined for " + quote("FixedPoint") + ".");
   endfunction
   function \~^ (in1, in2);
      return error ("The operator " + quote("~^") +
                    " is not defined for " + quote("FixedPoint") + ".");
   endfunction
   function \^ (in1, in2);
      return error ("The operator " + quote("^") +
                    " is not defined for " + quote("FixedPoint") + ".");
   endfunction
   function \| (in1, in2);
      return error ("The operator " + quote("|") +
                    " is not defined for " + quote("FixedPoint") + ".");
   endfunction
   function \& (in1, in2);
      return error ("The operator " + quote("&") +
                    " is not defined for " + quote("FixedPoint") + ".");
   endfunction

   function Bit#(1)  msb (FixedPoint#(i,f) in1);
      return msb (pack (in1));
   endfunction

   function Bit#(1)  lsb (FixedPoint#(i,f) in1);
      return lsb (pack (in1));
   endfunction

endinstance



//@ \index{fxptWrite@\te{fxptWrite} (fixed-point function)|textbf}
//@ Displaying \te{FixedPoint} values in a simple bit notation would
//@ result in a difficult to read pattern.  The following write
//@ utility function is provided to ease in their display.  Note
//@ that the use of this functions adds many multipliers and adders
//@ into the design which are only used for generating the
//@ output and not the actual circuit.
//@
//@ Displays a  \te{FixedPoint} value in a decimal format, where {\tt
//@ fwidth} give the number of digits to the right of the decimal
//@ point. {\tt fwidth} must be in the inclusive range of 0 to 10. The
//@ displayed result is truncated without rounding.
//@ # 2
function Action fxptWrite( Integer fwidth,
                           FixedPoint#(i,f) a )
   provisos(
            Add#(i, f, b),
            Add#(33,f,ff),      // 33 extra bits for computations.  10^10
            Min#(i,1,1)
            );
   action
      // this can be i bits, but iverilog gets confused!
      Int#(TAdd#(1,i))  ipart = extend(fxptGetInt(a));
      Bit#(f)           fpart = pack( fxptGetFrac( a ) ) ;

      // negate the fractional part if the integer part is less than 0
      if (( ipart < 0 ) && (fpart != 0))
         begin
            fpart = 0 - fpart ;
            ipart = ipart + 1;
            if ( ipart == 0 )
               $write( "-0." ) ;
            else
               $write( "%0d.", ipart ) ;
         end
      else
         $write( "%0d.", ipart ) ;

      Integer dispWidth = fwidth ;
      if ( fwidth < 0 || fwidth > 10 )
         begin
            let msg = "FixedPoint::fxptWrite Function fwidth argument must satisfy: "
                            + "0 <=fwidth <= 10. " + fromInteger( fwidth ) +
                            " is out of range."  ;
            dispWidth = error( msg ) ;
         end

      // Now for some machinery to generate the fractional part in a
      // decimal notation
      Integer idx ;
      Integer position = 1 ;
      Bit#(ff) taken = 0 ;
      for ( idx = 0 ; idx < dispWidth; idx = idx + 1 )
         begin
            position = position * 10 ;
            Bit#(ff) tx = (zeroExtend(fpart) * fromInteger(position) )  >>  fromInteger( valueOf( f ) ) ;
            Bit#(ff) tx2 = tx - taken ;
            Bit#(ff)  digit = tx2 & 'h0f ; // get the least 4 bits
            taken = 10 * (taken +  digit ) ;
            $write( "%0d",  digit ) ;
         end

   endaction
endfunction

instance FShow#(FixedPoint#(i,f));
   function Fmt fshow (FixedPoint#(i,f) value);
      Int#(i) i_part = fxptGetInt(value);
      UInt#(f) f_part = fxptGetFrac(value);
      return $format("<FP %b.%b>", i_part, f_part);
   endfunction
endinstance
