// -------------------------

function FixedPoint#(ri,rf)  fxptMult2 (
                                       FixedPoint#(ai,af) a,
                                       FixedPoint#(bi,bf) b )
   provisos(
             Add#(ai,bi,pi),
             Add#(af,bf,pf),
             Add#(xxG,ri,pi),
             Add#(xxH,rf,pf)
  
// The following 4 provisos are redundant
// And leaving them out, the compiler asks to add provisos with TAdds.
//            ,Add#(pi,pf, pb)
//            ,Add#(ai,af,ab)
//            ,Add#(bi,bf,bb)
//            ,Add#(ab,bb,pb)

            ) ;

   FixedPoint#(pi,pf) prod = fxptMult( a, b ) ;
   return fxptTruncate( prod ) ;
      
endfunction

// -------------------------

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

// -------------------------

function FixedPoint#(ri,rf)  fxptMult( FixedPoint#(ai,af) a,
                                       FixedPoint#(bi,bf) b  )
   provisos( Add#(ai,bi,ri)   // ri = ai + bi
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


// -------------------------

