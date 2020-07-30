
// BSC should not structural unify TAdd#(A,B) and TAdd#(X,Y),
// concluding here that ri==i and rf==f

function FixedPoint#(ri,rf) rebase(FixedPoint#(i,f) a)
   provisos(Bits#(FixedPoint#(ri,rf),x),
            Bits#(FixedPoint#(i,f),x) );
   return unpack(pack(a));
endfunction: rebase

// ----------

// Avoid dependency on the FixedPoint package, which could change

typedef struct {
                Int#(TAdd#(isize,fsize))  fxpt ;
                }
FixedPoint#(numeric type isize, numeric type fsize )
deriving( Eq, Bits ) ;

