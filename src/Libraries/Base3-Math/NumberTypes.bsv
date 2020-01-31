package NumberTypes;

// (1) WRAPNUMBER
// ==============

// A WrapNumber is an unsigned integer which wraps round.  They are to be used
// in situations where at any time all relevant values are in a small fraction
// of the value space.  Thus their ordering can be defined taking wrap-round
// into account, so that the nearer distance apart is used to determine which
// value is ahead of the other.

typedef struct { UInt#(sz) n; } WrapNumber#(numeric type sz)
      deriving (Bits, Eq, Arith, Literal, Bounded);

instance PrimIndex#(WrapNumber#(sz), sz);
   function isStaticIndex(x)  = isStaticIndex(x.n);
   function toStaticIndex(x)  = toStaticIndex(x.n);
   function toDynamicIndex(x) = toDynamicIndex(x.n);
endinstance

instance Ord#(WrapNumber#(n));
   function Bool \<=  (WrapNumber#(n) x, WrapNumber#(n) y) =
      ((y.n-x.n) < (x.n-y.n) || (x.n==y.n));
endinstance

// Utility functions to convert a WrapNumber to a UInt, and to add a UInt to a
// WrapNumber:

function WrapNumber#(sz) wrap(UInt#(sz) x) = WrapNumber { n: x };

function UInt#(sz) unwrap(WrapNumber#(sz) x) = x.n;

function WrapNumber#(n) addUInt(WrapNumber#(n) wn, UInt#(n) i) =
   WrapNumber {n: unwrap(wn) + i };

// (2) BUFFINDEX
// =============

// A BuffIndex is an unsigned integer which wraps round.  Unlike WrapNumbers
// (whose range is derived from their bitsize and is always a power of two),
// however, their range need not be a power of two, so we cannot simply use
// the hardware arithmetic.  They are intended as index types for buffers of
// arbitrary size, and therefore they have to be in the PrimIndex typeclass.
// They are not ordered -- you cannot tell which of two values is ahead of the
// other, because of wrap-round.

typedef struct { UInt#(sz) bix; } BuffIndex#(numeric type sz, numeric type ln)
   deriving (Bits, Eq);
// The two numeric type parameters are, respectively, the size in bits of the
// representation and the length of the buffer it is to index.

instance PrimIndex#(BuffIndex#(n,m), n);
   function isStaticIndex(a)  = isStaticIndex(pack(a));
   function toStaticIndex(a)  = toStaticIndex(pack(a));
   function toDynamicIndex(a) = toDynamicIndex(pack(a));
endinstance

// Literal constants are valid only if they are within the range of the buffer:
instance Literal#(BuffIndex#(n,m));
   function fromInteger(i) = BuffIndex {bix: fromInteger(i) };
   function inLiteralRange(x,i) = (i>=0 && i < valueof(m));
endinstance

// The only valid arithmetic operations are "+" and "-", which must take
// account of wrapround.  All the others are disabled:
instance Arith#(BuffIndex#(n,m))
   provisos(Add#(1, n, n1), Log#(m,log), Add#(log,_,n));

   function BuffIndex#(n,m) \+ (BuffIndex#(n,m) x, BuffIndex#(n,m) y);
      if (valueof(m)==valueof(TExp#(n)))
	 return BuffIndex {bix: x.bix+y.bix}; // rely on hardware wrap-round
      else
	 begin
	    let xx = x.bix;
	    let yy = y.bix;
	    let mm = fromInteger(valueof(m));
	    UInt#(n1) zz = extend(xx) + extend(yy);
	    if (zz >= mm) zz = zz - mm;
	    return BuffIndex {bix: truncate(zz) };
	 end
   endfunction

   function BuffIndex#(n,m) \- (BuffIndex#(n,m) x, BuffIndex#(n,m) y);
      if (valueof(m)==valueof(TExp#(n)))
	 return BuffIndex {bix: x.bix-y.bix}; // rely on hardware wrap-round
      else
	 begin
	    UInt#(n1) xx = extend(x.bix);
	    UInt#(n1) yy = extend(y.bix);
	    UInt#(n1) mm = fromInteger(valueof(m));

	    if (yy > xx) xx = xx + mm;
	    return BuffIndex {bix: truncate(xx-yy) };
	 end
   endfunction

   function BuffIndex#(n,m) negate(BuffIndex#(n,m) x) =
       error("The function " + quote("negate") + " is not defined for BuffIndex");
   function BuffIndex#(n,m) \* (BuffIndex#(n,m) x, BuffIndex#(n,m) y) =
       error("The function " + quote("*") + " is not defined for BuffIndex");
   function BuffIndex#(n,m) \/ (BuffIndex#(n,m) x, BuffIndex#(n,m) y) =
       error("The function " + quote("/") + " is not defined for BuffIndex");
   function BuffIndex#(n,m) \% (BuffIndex#(n,m) x, BuffIndex#(n,m) y) =
       error("The function " + quote("%") + " is not defined for BuffIndex");
endinstance

// Utility functions for converting a BuffIndex to a UInt and for adding and
// subtracting BuffIndexes and UInts:

function UInt#(n) unwrapBI(BuffIndex#(n,m) x) = x.bix;

function BuffIndex#(n,m) addBIUInt(BuffIndex#(n,m) bin, UInt#(n) i)
   provisos(Arith#(BuffIndex#(n,m)));
   UInt#(TAdd#(n,1)) cycle = fromInteger(valueOf(m));
   return (extend(i)>=cycle ? (?) : bin + BuffIndex {bix: i });
endfunction

function BuffIndex#(n,m) sbtrctBIUInt(BuffIndex#(n,m) bin, UInt#(n) i)
   provisos(Arith#(BuffIndex#(n,m)));
   UInt#(TAdd#(n,1)) cycle = fromInteger(valueOf(m));
   return (extend(i)>=cycle ? (?) : bin - BuffIndex {bix: i });
endfunction

endpackage
