// Reduce the integer size of a fixed point value, truncating
function FixedPoint#(ri,f) dropMSBs(FixedPoint#(i,f) a)
   provisos(Add#(_,TAdd#(ri,f),TAdd#(i,f)));
   return unpack(truncate(pack(a)));
endfunction: dropMSBs

// Fixed-point division.  The return type must have enough integer bits to
// contain the result of the division, or else the return value is undefined.
function FixedPoint#(ri,nf) fxptDivide(FixedPoint#(ni,nf) num,
                                       FixedPoint#(di,df) denom)
   provisos(
      // define the sizes "sz", "sz2", and "sz3" to be used in the body
      Add#(ni,nf,sz), Add#(df,sz,sz2), Add#(ni,df,sz3)

      // this is needed, because "di" is not mentioned above
      // (it's saying that width of "denom" is LTE width of "num")
      ,Add#(_1, TAdd#(di,df), sz2)
      // this is needed, because "ri" is not mentioned above
      // (the result int component must be LTE "sz3" == ni+df)
      ,Add#(_2,ri,sz3)

      // XXX this can be figured out from the first three Add provisos
      ,Add#(sz3, nf, sz2)
   );
   Int#(sz2) n = unpack(signExtend(pack(num))) << valueOf(df);
   Int#(sz2) d = unpack(signExtend(pack(denom)));
   Int#(sz2) q = n / d;
   FixedPoint#(sz3,nf) out = unpack(pack(q));
   return dropMSBs(out);
endfunction: fxptDivide

// ----------------------------------------------------------------------

typedef struct {
                Bit#(isize) i;
                Bit#(fsize) f;
                }
FixedPoint#(numeric type isize, numeric type fsize )
deriving( Eq ) ;

function FixedPoint#(i,f) epsilon () ;
      Int#(b)  eps = 'b01  ;
      return _fromInternal (eps);
endfunction

function FixedPoint#(i,f)  _fromInternal ( Int#(b) x )
   provisos ( Add#(i,f,b) );
   return unpack ( pack (x) );
endfunction

function  Int#(b) _toInternal ( FixedPoint#(i,f) x )
   provisos ( Add#(i,f,b) );
   return unpack ( pack (x) );
endfunction

function Int#(isize) fxptGetInt ( FixedPoint#(isize, fsize) a );
   return unpack (a.i);
endfunction

function UInt#(fsize) fxptGetFrac ( FixedPoint#(isize, fsize) a );
   return unpack (a.f);
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

instance Arith#( FixedPoint#(i,f) )
   provisos( Add#(i,f,b) );

   // Addition does not change the binary point
   function FixedPoint#(i,f) \+ (FixedPoint#(i,f) in1, FixedPoint#(i,f) in2 );
       return _fromInternal ( _toInternal (in1) + _toInternal (in2) ) ;
   endfunction

   // For multiplication, the computation is accomplished in full
   // precision, and the result truncated to fit
   function FixedPoint#(i,f) \* (FixedPoint#(i,f) in1, FixedPoint#(i,f) in2 )
      provisos(Add#(b,b,doublesize) ) ;
      // define some double sized operands for computations
      Int#(b) a1 = _toInternal(in1);
      Int#(b) a2 = _toInternal(in2);
      Int#(doublesize) m1, m2, prod ;

      m1 = signExtend( a1 ) ;
      m2 = signExtend( a2 ) ;
      prod = m1 * m2 ;
      // truncate the fractional bit
      prod = prod >> fromInteger(valueOf(f)) ;
      // Now truncate the integer part before placing it into the structure.
      Int#(b) finalv = truncate( prod ) ;
      return _fromInternal (finalv);
   endfunction

   // The rest are not needed for this design

   function FixedPoint#(i,f) \- (FixedPoint#(i,f) in1, FixedPoint#(i,f) in2 );
      return error ("The operator " + quote("-") +
                    " is not defined for " + quote("FixedPoint") + ".");
   endfunction

   function FixedPoint#(i,f) negate (FixedPoint#(i,f) in1 );
      return error ("The function " + quote("negate") +
                    " is not defined for " + quote("FixedPoint") + ".");
   endfunction

   function FixedPoint#(i,f) \/ (FixedPoint#(i,f) in1, FixedPoint#(i,f) in2);
      return error ("The operator " + quote("/") +
                    " is not defined for " + quote("FixedPoint") + ".");
   endfunction

   function FixedPoint#(i,f) \% (FixedPoint#(i,f) in1, FixedPoint#(i,f) in2);
      return error ("The operator " + quote("%") +
                    " is not defined for " + quote("FixedPoint") + ".");
   endfunction

   function FixedPoint#(i,f) abs( FixedPoint#(i,f) x);
      return error ("The function " + quote("abs") +
                    " is not defined for " + quote("FixedPoint") + ".");
   endfunction

   function FixedPoint#(i,f) signum( FixedPoint#(i,f) x);
      return error ("The function " + quote("signum") +
                    " is not defined for " + quote("FixedPoint") + ".");
   endfunction

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

instance Literal#( FixedPoint#(i,f) )
   provisos( Add#(i,f,b) );

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

instance Ord#( FixedPoint#(i,f) )
   provisos( Add#(i,f,b) );

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

instance Bitwise#( FixedPoint#(i,f) )
   provisos (Add#(i,f,b)
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

function FixedPoint#(i,f) fromRational( Integer numerator, Integer denominator)
   provisos ( //Add#(1, xxA, i )          // i >= 1
             Add#(i,f,b) );
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

function FixedPoint#(ri,rf)  fxptMult( FixedPoint#(ai,af) a,
                                       FixedPoint#(bi,bf) b  )
   provisos (Add#(ai,bi,ri)   // ri = ai + bi
             ,Add#(af,bf,rf)   // rf = af + bf
             ,Add#(ai,af,ab)
             ,Add#(bi,bf,bb)
             ,Add#(ab,bb,rb)
             ,Add#(ri,rf,rb)
            ) ;

   Int#(ab) ap = _toInternal(a);
   Int#(bb) bp = _toInternal(b);

   Int#(rb) prod = signedMul(ap, bp); // signed integer multiplication

   return _fromInternal(prod);

endfunction

function FixedPoint#(ri,rf) fxptTruncate( FixedPoint#(ai,af) a )
   provisos( Add#(xxA,ri,ai),    // ai >= ri
             Add#(xxB,rf,af)    // af >= rf
            ) ;

   FixedPoint#(ri,rf) res = FixedPoint {i: truncate (a.i),
                                        f: truncateLSB (a.f) } ;
   return res;

endfunction

function Action fxptWrite( Integer fwidth,
                           FixedPoint#(i,f) a )
   provisos(
            Add#(i, f, b),
            Add#(33,f,ff)      // 33 extra bits for computations.  10^10
            );
   action
      Int#(i)           ipart = fxptGetInt( a ) ;
      Bit#(f)           fpart = pack( fxptGetFrac( a ) ) ;

      // negate the fractional part if the integer part is less than 0
      if (( ipart < 0 ) && (fpart != 0))
         begin
            fpart = 0 - fpart ;
            ipart = unpack( pack(ipart) + 1 );
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

// ----------------------------------------------------------------------

