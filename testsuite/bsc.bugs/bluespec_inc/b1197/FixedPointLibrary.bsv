import FixedPoint::*;
import TypeClasses::*;

instance Extend#(FixedPoint#(ni,nf), FixedPoint#(mi,mf))
    provisos(Add#(xxa,ni,mi),
	     Add#(xxb,nf,mf),
	     Add#(xxc,TAdd#(ni,nf),TAdd#(mi,mf)),
	     Min#(ni, 1, 1));

  function FixedPoint#(mi,mf) grow(FixedPoint#(ni,nf) x)
    provisos(Add#(xxa,ni,mi),
	     Add#(xxb,nf,mf),
	     Add#(xxc,TAdd#(ni,nf),TAdd#(mi,mf)));

      return fxptSignExtend(x);
  endfunction // FixedPoint

  function FixedPoint#(ni,nf) shrink(FixedPoint#(mi,mf) x)
      provisos(Add#(xxa,ni,mi),
	       Add#(xxb,nf,mf),
	       Add#(xxc,TAdd#(ni,nf),TAdd#(mi,mf)));
      return fxptTruncate(x);
  endfunction // FixedPoint

endinstance