
typedef struct { UInt#(TLog#(sz)) bix; } BuffIndex#(numeric type sz)
      deriving (Bits, Eq, Literal);

instance Arith#(BuffIndex#(n));

   function BuffIndex#(n) \+ (BuffIndex#(n) x, BuffIndex#(n) y);
      let xx = x.bix;
      let yy = y.bix;
      let nn = fromInteger(valueof(n));
      UInt#(TAdd#(1,TLog#(n))) zz = extend(xx) + extend(yy);
      if (zz > nn) zz = zz - nn;
      return BuffIndex {bix: truncate(zz) };
   endfunction

   function BuffIndex#(n) \- (BuffIndex#(n) x, BuffIndex#(n) y);
      UInt#(TAdd#(1,TLog#(n))) xx = extend(x.bix);
      UInt#(TAdd#(1,TLog#(n))) yy = extend(y.bix);
      UInt#(TAdd#(1,TLog#(n))) nn = fromInteger(valueof(n));

      if (yy > xx) xx = xx + nn;
      return BuffIndex {bix: truncate(xx-yy) };
   endfunction

   function BuffIndex#(n) negate(BuffIndex#(n) x) =
       error("The function " + quote("negate") + " is not defined for BuffIndex");

   function BuffIndex#(n) \* (BuffIndex#(n) x, BuffIndex#(n) y) =
       error("The function " + quote("*") + " is not defined for BuffIndex");
   function BuffIndex#(n) \/ (BuffIndex#(n) x, BuffIndex#(n) y) =
       error("The function " + quote("/") + " is not defined for BuffIndex");
   function BuffIndex#(n) \% (BuffIndex#(n) x, BuffIndex#(n) y) =
       error("The function " + quote("%") + " is not defined for BuffIndex");
endinstance

