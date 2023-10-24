// Some utility functions and modules

import Complex::*;
import FixedPoint::*;

// (*noinline*)
// function FixedPoint#(2,1) d1 (FixedPoint#(7,2) x);
//    return fxptTruncateRound(Rnd_Plus_Inf,x);

// endfunction




// FixedPoint addition with Saturation
// Additions are carried out with 1 additional bit
function  FixedPoint#(ri,rf) fxptAddSat ( SaturationMode smode, FixedPoint#(ri,rf) x,  FixedPoint#(ri,rf) y) = satPlus(smode, x, y);



function Complex#(t) cmplxAddWith (function t adder   (t aa, t bb)
                                   ,Complex# (t) x
                                   ,Complex# (t) y );
   return cmplx(adder(x.rel, y.rel), adder(x.img, y.img));
endfunction


// Complex# (FixedPoint) Multiplication using fullmult function as
// the multiplier.   This allows full precision multiplication
function Complex#(t) cmplxFullMult (function t fullmult (r aa, s bb)
                                    ,function t adder   (t aa, t bb)
                                    ,Complex# (r) x
                                    ,Complex# (s) y )
   provisos (Arith#(t));
   r  a = x.rel;
   r  b = x.img;
   s  c = y.rel;
   s  d = y.img;

   t ac = fullmult(a,c);
   t ad = fullmult(a,d);
   t bc = fullmult(b,c);
   t bd = fullmult(b,d);
   return cmplx (adder(ac,-bd), adder(ad,bc));
endfunction

// Complex# (FixedPoint) Multiplication where fixed point sizes differ
// Full multiplication
function Complex#(FixedPoint#(ri,rf)) c_fxptMult (SaturationMode smode
                                                  ,Complex# (FixedPoint#(ai,af)) x
                                                  ,Complex# (FixedPoint#(bi,bf)) y )
   provisos ( Min#(ai, 1, 1)
             ,Min#(bi, 1, 1)
             ,Add#(ai,bi,ri)   // ri = ai + bi
             ,Add#(af,bf,rf)   // rf = af + bf
             ,Add#(ai,af,ab)
             ,Add#(bi,bf,bb)
             ,Add#(ab,bb,rb)
             ,Add#(ri,rf,rb)
             ,Add#(TAdd#(ri, ri), TAdd#(rf, rf), TAdd#(rb, rb))
             ) ;
   return cmplxFullMult (fxptMult, fxptAddSat(smode), x, y);
endfunction

function Complex#(FixedPoint#(ri,rf)) c_fxptAddSat (SaturationMode smode
                                                    ,Complex# (FixedPoint#(ri,rf)) x
                                                    ,Complex# (FixedPoint#(ri,rf)) y );
   return cmplxAddWith (fxptAddSat(smode), x, y);
endfunction
