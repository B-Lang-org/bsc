////////////////////////////////////////////////////////////////////////////////
//  Filename      : FloatingPoint.bsv
//  Description   : General purpose floating point library
////////////////////////////////////////////////////////////////////////////////
package FloatingPoint;

// Notes :
// increasing exp = right shift sfd
// decreasing exp = left shift sfd

////////////////////////////////////////////////////////////////////////////////
/// Imports
////////////////////////////////////////////////////////////////////////////////
import Real              ::*;
import Vector            ::*;
import BUtils            ::*;
import GetPut            ::*;
import ClientServer      ::*;
import FIFO              ::*;
import FixedPoint        ::*;

////////////////////////////////////////////////////////////////////////////////
/// Exports
////////////////////////////////////////////////////////////////////////////////
export Disorder(..);
export Double;
export DoubleExtended;
export Exception(..);
export FixedFloatCVT(..);
export Float;
export FloatingPoint(..);
export Half;
export RoundMode(..);
export addFP;
export compareFP;
export convert;
export divFP;
export fract;
export infinity;
export isInfinity;
export isNaN;
export isNegativeZero;
export isOne;
export isQNaN;
export isSNaN;
export isSubNormal;
export isZero;
export mkFloatingPointAdder;
export mkFloatingPointDivider;
export mkFloatingPointFusedMultiplyAccumulate;
export mkFloatingPointMultiplier;
export mkFloatingPointSquareRooter;
export multFP;
export nanQuiet;
export one;
export qnan;
export snan;
export sqrtFP;
export zero;

////////////////////////////////////////////////////////////////////////////////
/// Types
////////////////////////////////////////////////////////////////////////////////

typedef struct {
   Bool        sign;
   Bit#(e)     exp;
   Bit#(m)     sfd;
} FloatingPoint#(numeric type e, numeric type m) deriving (Bits);

instance DefaultValue#( FloatingPoint#(e,m) );
   defaultValue = FloatingPoint {
      sign:       False,
      exp:        0,
      sfd:        0
      };
endinstance

typedef enum {
   LT,
   EQ,
   GT,
   UO
   } Disorder deriving (Bits, Eq, Bounded);

////////////////////////////////////////////////////////////////////////////////
/// Eq
////////////////////////////////////////////////////////////////////////////////
instance Eq#(FloatingPoint#(e,m));
   function Bool \== ( FloatingPoint#(e,m) a, FloatingPoint#(e,m) b );
      let c = compareFP(a, b);
      return (c == EQ);
   endfunction

   function Bool \/= ( FloatingPoint#(e,m) a, FloatingPoint#(e,m) b );
      let c = compareFP(a, b);
      return (c != EQ);
   endfunction
endinstance

instance FShow#( FloatingPoint#(e,m) );
   function Fmt fshow( FloatingPoint#(e,m) value );
      return $format("<Float %s%x.%x>", value.sign ? "-" : "+", value.exp, value.sfd);
   endfunction
endinstance

instance Bounded#(FloatingPoint#(e,m));
   minBound = FloatingPoint {
      sign: True,
      exp: ('1 - 1),
      sfd: '1
      };
   maxBound = FloatingPoint {
      sign: False,
      exp: ('1 - 1),
      sfd: '1
      };
endinstance

typedef enum {
     Rnd_Nearest_Even
   , Rnd_Nearest_Away_Zero
   , Rnd_Plus_Inf
   , Rnd_Minus_Inf
   , Rnd_Zero
} RoundMode deriving (Bits, Eq);

instance DefaultValue#(RoundMode);
   defaultValue = Rnd_Nearest_Even;
endinstance

instance FShow#( RoundMode );
   function Fmt fshow( RoundMode value );
      case(value)
	 Rnd_Nearest_Even:      return $format("<Round Mode: Nearest Even>");
	 Rnd_Nearest_Away_Zero: return $format("<Round Mode: Nearest Away From Zero>");
	 Rnd_Plus_Inf:          return $format("<Round Mode: +Infinity>");
	 Rnd_Minus_Inf:         return $format("<Round Mode: -Infinity>");
	 Rnd_Zero:              return $format("<Round Mode: Zero>");
      endcase
   endfunction
endinstance

typedef struct {
   Bool invalid_op;
   Bool divide_0;
   Bool overflow;
   Bool underflow;
   Bool inexact;
} Exception deriving (Bits, Eq);

instance DefaultValue#(Exception);
   defaultValue = unpack(0);
endinstance

instance Bitwise#(Exception);
   function Exception \& (Exception x1, Exception x2);
      return unpack(pack(x1) & pack(x2));
   endfunction
   function Exception \| (Exception x1, Exception x2);
      return unpack(pack(x1) | pack(x2));
   endfunction
   function Exception \^ (Exception x1, Exception x2);
      return unpack(pack(x1) ^ pack(x2));
   endfunction
   function Exception \~^ (Exception x1, Exception x2);
      return unpack(pack(x1) ~^ pack(x2));
   endfunction
   function Exception \^~ (Exception x1, Exception x2);
      return unpack(pack(x1) ^~ pack(x2));
   endfunction
   function Exception invert (Exception x1);
      return unpack(~pack(x1));
   endfunction
   function Exception \<< (Exception x1, ix x2)
     provisos(PrimShiftIndex#(ix,dx));
      return error("Bitwise left shift not supported for type " + quote("Exception"));
   endfunction
   function Exception \>> (Exception x1, ix x2)
     provisos(PrimShiftIndex#(ix,dx));
      return error("Bitwise right shift not supported for type " + quote("Exception"));
   endfunction
   function Bit#(1) msb (Exception x);
      return error("Bitwise msb() not supported for type " + quote("Exception"));
   endfunction
   function Bit#(1) lsb (Exception x);
      return error("Bitwise lsb() not supported for type " + quote("Exception"));
   endfunction
endinstance

instance FShow#( Exception );
   function Fmt fshow( Exception value );
      Fmt f = $format("<Exception: ");
      if (value.invalid_op)
	 f = f + $format("Invalid_Op ");
      if (value.divide_0)
	 f = f + $format("Divide_0 ");
      if (value.overflow)
	 f = f + $format("Overflow ");
      if (value.underflow)
	 f = f + $format("Underflow ");
      if (value.inexact)
	 f = f + $format("Inexact ");
      f = f + $format(">");
      return f;
   endfunction
endinstance

////////////////////////////////////////////////////////////////////////////////
/// Float Formats
////////////////////////////////////////////////////////////////////////////////
typedef FloatingPoint#(5,10)  Half;
typedef FloatingPoint#(8,23)  Float;
typedef FloatingPoint#(11,32) SingleExtended;
typedef FloatingPoint#(11,52) Double;
typedef FloatingPoint#(15,64) DoubleExtended;

function Tuple2#(FloatingPoint#(e2,m2),Exception) convert(FloatingPoint#(e,m) in, RoundMode rmode, Bool preservenan)
   provisos(
      Max#(e, e2, emax),
      Max#(m, m2, mmax),
      Add#(emax, 1, expbits),
      Add#(mmax, 5, sfdbits),
      // per request of bsc
      Add#(a__, e, TAdd#(TMax#(e, e2), 1)),
      Add#(b__, e2, TAdd#(TMax#(e, e2), 1)),
      Add#(c__, TLog#(TAdd#(1, m)), expbits),
      Add#(d__, e2, expbits),
      Add#(m2, e__, sfdbits),
      Add#(f__, e, expbits),
      Add#(2, g__, sfdbits),
      Add#(1, TAdd#(1, TAdd#(m2, TAdd#(2, h__))), sfdbits),
      Add#(4, h__, e__),
      Add#(i__, TLog#(TAdd#(1, sfdbits)), TAdd#(e2, 1))
      );

   FloatingPoint#(e2,m2) out = defaultValue;
   Exception exc = defaultValue;

   if (isNaN(in)) begin
      if (isSNaN(in) && !preservenan) begin
	 in = nanQuiet(in);
	 exc.invalid_op = True;
      end

      out.sign = in.sign;
      out.exp = '1;
      Bit#(sfdbits) sfd = zExtendLSB(in.sfd);
      out.sfd = truncateLSB(sfd);
      if (out.sfd == 0)
	 out.sfd = zExtendLSB(2'b01);
   end
   else if (isInfinity(in))
      out = infinity(in.sign);
   else if (isZero(in))
      out = zero(in.sign);
   else if (isSubNormal(in)) begin
      Int#(expbits) exp = fromInteger(minexp(in));
      Bit#(sfdbits) sfd = zExtendLSB({1'b0, getHiddenBit(in),in.sfd});
      Int#(expbits) subexp = unpack(pack(extend(countZerosMSB(in.sfd))));

      if ((exp - subexp) > fromInteger(maxexp(out))) begin
	 out.sign = in.sign;
	 out.exp = maxBound - 1;
	 out.sfd = maxBound;

	 exc.overflow = True;
	 exc.inexact = True;

	 let y = round(rmode, out, '1);
	 out = tpl_1(y);
	 exc = exc | tpl_2(y);
      end
      else if ((exp - subexp) < fromInteger(minexp(out))) begin
	 out.sign = in.sign;
	 out.exp = 0;  // subnormal

	 let shift = fromInteger(abs(minexp(in)) - abs(minexp(out)));
	 if (shift < 0) begin
	    sfd = sfd << (-shift);
	 end
	 else if (shift < fromInteger(valueOf(sfdbits))) begin
	    Bit#(1) guard = |(sfd << (fromInteger(valueOf(sfdbits)) - shift));

	    sfd = sfd >> shift;
	    sfd[0] = sfd[0] | guard;
	 end
	 else if (|sfd == 1) begin
	    sfd = 1;
	 end

	 let x = normalize(out, sfd);
	 out = tpl_1(x);
	 exc = exc | tpl_3(x);

	 if (isZero(out)) begin
	    exc.underflow = True;
	 end

	 let y = round(rmode, out, tpl_2(x));
	 out = tpl_1(y);
	 exc = exc | tpl_2(y);
      end
      else begin
	 out.sign = in.sign;
	 out.exp = pack(truncate(exp + fromInteger(bias(out))));

	 let x = normalize(out, sfd);
	 out = tpl_1(x);
	 exc = exc | tpl_3(x);

	 let y = round(rmode, out, tpl_2(x));
	 out = tpl_1(y);
	 exc = exc | tpl_2(y);
      end
   end
   else begin
      Int#(expbits) exp = signExtend(unpack(unbias(in)));
      Bit#(sfdbits) sfd = zExtendLSB({1'b0, getHiddenBit(in),in.sfd});

      if (exp > fromInteger(maxexp(out))) begin
	 out.sign = in.sign;
	 out.exp = maxBound - 1;
	 out.sfd = maxBound;

	 exc.overflow = True;
	 exc.inexact = True;

	 let y = round(rmode, out, '1);
	 out = tpl_1(y);
	 exc = exc | tpl_2(y);
      end
      else if (exp < fromInteger(minexp(out))) begin
	 out.sign = in.sign;
	 out.exp = 0;  // subnormal

	 let shift = (fromInteger(minexp(out)) - exp);
	 if (shift < fromInteger(valueOf(sfdbits))) begin
	    Bit#(1) guard = |(sfd << (fromInteger(valueOf(sfdbits)) - shift));

	    sfd = sfd >> shift;
	    sfd[0] = sfd[0] | guard;
	 end
	 else if (|sfd == 1) begin
	    sfd = 1;
	 end

	 let x = normalize(out, sfd);
	 out = tpl_1(x);
	 exc = exc | tpl_3(x);

	 if (isZero(out)) begin
	    exc.underflow = True;
	 end

	 let y = round(rmode, out, tpl_2(x));
	 out = tpl_1(y);
	 exc = exc | tpl_2(y);
      end
      else begin
	 out.sign = in.sign;
	 out.exp = pack(truncate(exp + fromInteger(bias(out))));

	 let x = normalize(out, sfd);
	 out = tpl_1(x);
	 exc = exc | tpl_3(x);

	 let y = round(rmode, out, tpl_2(x));
	 out = tpl_1(y);
	 exc = exc | tpl_2(y);
      end
   end

   return tuple2(out, exc);
endfunction

////////////////////////////////////////////////////////////////////////////////
/// Functions
////////////////////////////////////////////////////////////////////////////////
// Zero extend a quantity by padding on the LSB side.
function Bit#(m) zExtendLSB(Bit#(n) value)
   provisos( Add#(n,m,k) );
   Bit#(k) out = { value, 0 };
   return out[valueof(k)-1:valueof(n)];
endfunction

// Zero extend and change type by padding on the LSB side (of bits instance)
function a cExtendLSB(b value)
   provisos( Bits#(a,sa), Bits#(b,sb) );
   let out = unpack(zExtendLSB(pack(value)));
   return out;
endfunction

// Returns the 1-based index (or 0 if not found) of the first 1
// from the MSB down.
function Integer findIndexOneMSB_( Bit#(s) din );
   Vector#(s, Bit#(1)) v = unpack(din);
   Integer result = 0;
   for(Integer i = 0; i < valueof(s); i = i + 1) begin
      if (v[i] == 1) result = i + 1;
   end
   return result;
endfunction

function UInt#(l) findIndexOneMSB( Bit#(s) din )
   provisos( Add#(_, 1, s), Log#(s, logs), Add#(logs,1,l));
   Vector#(s, Bit#(1)) v = unpack(reverseBits(din));
   if (findElem(1'b1, v) matches tagged Valid .ridx) begin
      return fromInteger(valueOf(s)) - cExtend(ridx);
   end
   else begin
      return 0;
   end
endfunction

// Returns the 1-based index (or 0 if not found) of the first 1
// from the LSB up.
function Integer findIndexOneLSB_( Bit#(s) din );
   Vector#(s, Bit#(1)) v = unpack(din);
   Integer result = 0;
   Bool done = False;
   for(Integer i = 0; i < valueof(s); i = i + 1) begin
      if (v[i] == 1)  done = True;
      else if (!done) result = i + 1;
   end
   return (done) ? result : 0;
endfunction

function UInt#(l) findIndexOneLSB( Bit#(s) din )
   provisos( Add#(_, 1, s), Log#(s, logs), Add#(logs,1,l));
   Vector#(s, Bit#(1)) v = unpack(din);
   if (findElem(1'b1, v) matches tagged Valid .ridx) begin
      return cExtend(ridx);
   end
   else begin
      return 0;
   end
endfunction


function FloatingPoint#(e,m) infinity(Bool sign);
   return FloatingPoint {
      sign:     sign,
      exp:      maxBound,
      sfd:      0
      };
endfunction

function Bool isInfinity( FloatingPoint#(e,m) din );
   return ((&din.exp == 1) && (din.sfd == 0));
endfunction

function FloatingPoint#(e,m) qnan();
   return FloatingPoint {
      sign:     False,
      exp:      '1,
      sfd:      reverseBits('b1)
      };
endfunction

function Bool isQNaN( FloatingPoint#(e,m) din );
   return ((&din.exp == 1) && (msb(din.sfd) == 1));
endfunction

function FloatingPoint#(e,m) snan();
   return FloatingPoint {
      sign:     False,
      exp:      '1,
      sfd:      reverseBits('b10)
      };
endfunction

function Bool isSNaN( FloatingPoint#(e,m) din );
   return ((&din.exp == 1) && (|din.sfd == 1) && (msb(din.sfd) == 0));
endfunction

function FloatingPoint#(e,m) nanQuiet(FloatingPoint#(e,m) din);
   din.sfd = din.sfd | reverseBits('b1);
   return din;
endfunction

function FloatingPoint#(e,m) zero(Bool sign);
   return FloatingPoint {
      sign:     sign,
      exp:      0,
      sfd:      0
      };
endfunction

function FloatingPoint#(e,m) one(Bool sign);
   FloatingPoint#(e,m) dummy = ?;
   return FloatingPoint {
      sign:     sign,
      exp:      fromInteger(bias(dummy)),
      sfd:      0
      };
endfunction

function Bool isZero( FloatingPoint#(e,m) din );
   return isSubNormal(din) && (din.sfd == 0);
endfunction

function Bool isOne( FloatingPoint#(e,m) din );
   return (din.sfd == 0) && (din.exp == fromInteger(bias(din)));
endfunction

function Bool isNegativeZero( FloatingPoint#(e,m) din );
   return isZero(din) && (din.sign);
endfunction

function Bool isNaN( FloatingPoint#(e,m) din );
   return isNaNOrInfinity(din) && !isInfinity(din);
endfunction

function Bool isNaNOrInfinity( FloatingPoint#(e,m) din );
   return (din.exp == '1);
endfunction

function Bool isSubNormal( FloatingPoint#(e,m) din );
   return (din.exp == 0);
endfunction

function Integer bias( FloatingPoint#(e,m) din );
   return (2 ** (valueof(e)-1)) - 1;
endfunction

function Bit#(e) unbias( FloatingPoint#(e,m) din );
   return (din.exp - fromInteger(bias(din)));
endfunction

function Bit#(1) getHiddenBit( FloatingPoint#(e,m) din );
   return (isSubNormal(din)) ? 0 : 1;
endfunction

function Integer minexp( FloatingPoint#(e,m) din );
  return 1-bias(din);
endfunction

function Integer minexp_subnormal( FloatingPoint#(e,m) din );
   return minexp(din)-valueof(m);
endfunction

function Integer maxexp( FloatingPoint#(e,m) din );
   return bias(din);
endfunction

function FloatingPoint#(e,m) rightshift( FloatingPoint#(e,m) din, Bit#(e) amt )
   provisos(  Add#(m, 4, m4)
	    , Add#(m4, m, x)
	    );
   Bit#(x) sfd = cExtendLSB({ getHiddenBit(din), din.sfd });
   Bit#(1) hidden;
   Bit#(m) s;
   Bit#(m) rest;
   { hidden, s, rest } = cExtendLSB(sfd >> amt);
   din.sfd    = s;
   return din;
endfunction

function Tuple2#(FloatingPoint#(e,m),Exception) round( RoundMode rmode, FloatingPoint#(e,m) din, Bit#(2) guard )
   provisos(  Add#(m, 1, m1)
	    , Add#(m, 2, m2)
	    );

   FloatingPoint#(e,m) out = defaultValue;
   Exception exc = defaultValue;

   if (isNaNOrInfinity(din)) begin
      out = din;
   end
   else begin
      let din_inc = din;

      Bit#(TAdd#(m,2)) sfd = unpack({1'b0, getHiddenBit(din), din.sfd}) + 1;

      if (msb(sfd) == 1) begin
	 if (din.exp == fromInteger(maxexp(din) + bias(out))) begin
	    din_inc = infinity(din_inc.sign);
	 end
	 else begin
	    din_inc.exp = din_inc.exp + 1;
	    din_inc.sfd = truncate(sfd >> 1);
	 end
      end
      else if ((din.exp == 0) && (truncateLSB(sfd) == 2'b01)) begin
	 din_inc.exp = 1;
	 din_inc.sfd = truncate(sfd);
      end
      else begin
	 din_inc.sfd = truncate(sfd);
      end

      if (guard != 0) begin
	 exc.inexact = True;
      end

      case(rmode)
	 Rnd_Nearest_Even:
	 begin
	    case (guard)
	       'b00: out = din;
	       'b01: out = din;
	       'b10: out = (lsb(din.sfd) == 1) ? din_inc : din;
	       'b11: out = din_inc;
	    endcase
	 end

	 Rnd_Nearest_Away_Zero:
	 begin
	    case (guard)
	       'b00: out = din;
	       'b01: out = din_inc;
	       'b10: out = din_inc;
	       'b11: out = din_inc;
	    endcase
	 end

	 Rnd_Plus_Inf:
	 begin
	    if (guard == 0)
	       out = din;
	    else if (din.sign)
	       out = din;
	    else
	       out = din_inc;
	 end

	 Rnd_Minus_Inf:
	 begin
	    if (guard == 0)
	       out = din;
	    else if (din.sign)
	       out = din_inc;
	    else
	       out = din;
	 end

	 Rnd_Zero:
	 begin
	    out = din;
	 end
      endcase
   end

   if (isInfinity(out)) begin
      exc.overflow = True;
   end

   return tuple2(out,exc);
endfunction

function Tuple3#(FloatingPoint#(e,m),Bit#(2),Exception) normalize( FloatingPoint#(e,m) din, Bit#(x) sfdin )
   provisos(
      Add#(1, a__, x),
      Add#(m, b__, x),
      // per request of bsc
      Add#(c__, TLog#(TAdd#(1, x)), TAdd#(e, 1))
      );

   FloatingPoint#(e,m) out = din;
   Bit#(2) guard = 0;
   Exception exc = defaultValue;

   Int#(TAdd#(e,1)) exp = isSubNormal(out) ? fromInteger(minexp(out)) : signExtend(unpack(unbias(out)));
   let zeros = countZerosMSB(sfdin);

   if ((zeros == 0) && (exp == fromInteger(maxexp(out)))) begin
      out.exp = maxBound - 1;
      out.sfd = maxBound;
      guard = '1;
      exc.overflow = True;
      exc.inexact = True;
   end
   else begin
      if (zeros == 0) begin
	 // carry, no sfd adjust necessary

	 if (out.exp == 0)
	    out.exp = 2;
	 else
	    out.exp = out.exp + 1;

	 // carry bit
	 sfdin = sfdin << 1;
      end
      else if (zeros == 1) begin
	 // already normalized

	 if (out.exp == 0)
	    out.exp = 1;

	 // carry, hidden bits
	 sfdin = sfdin << 2;
      end
      else if (zeros == fromInteger(valueOf(x))) begin
	 // exactly zero
	 out.exp = 0;
      end
      else begin
	 // try to normalize
	 Int#(TAdd#(e,1)) shift = zeroExtend(unpack(pack(zeros - 1)));
	 Int#(TAdd#(e,1)) maxshift = exp - fromInteger(minexp(out));

	 if (shift > maxshift) begin
	    // result will be subnormal

	    sfdin = sfdin << maxshift;
	    out.exp = 0;
	 end
	 else begin
	    // result will be normal

	    sfdin = sfdin << shift;
	    out.exp = out.exp - truncate(pack(shift));
	 end

 	 // carry, hidden bits
	 sfdin = sfdin << 2;
      end

      out.sfd = unpack(truncateLSB(sfdin));
      sfdin = sfdin << fromInteger(valueOf(m));

      guard[1] = unpack(truncateLSB(sfdin));
      sfdin = sfdin << 1;

      guard[0] = |sfdin;
   end

   if ((out.exp == 0) && (guard != 0))
      exc.underflow = True;

   return tuple3(out,guard,exc);
endfunction

function Tuple2#(FloatingPoint#(e,m),Exception) fract(FloatingPoint#(e,m) din)
   provisos(
      // per request of bsc
      Add#(a__, TLog#(TAdd#(1, TAdd#(1, TAdd#(TAdd#(m, 1), 1)))), TAdd#(e, 1))
      );
   FloatingPoint#(e,m) res = din;
   Exception exc = defaultValue;

   // this routine extracts the fractional portion of a floating point number, i.e.
   //  123.456 would return 0.456.

   // if the value is not a number, provide not a number result
   if (isNaN(din))
      res = din;
   else if (isInfinity(din)) // if the number is infinity, signal NaN
      res = qnan();
   else if (din.exp < fromInteger(bias(din))) // 0 <= quantity < 1
      res = din;
   else begin // all other cases
      Bit#(TAdd#(m,1)) m = { 1'b1, din.sfd };
      m = m << (din.exp - fromInteger(bias(din)) + 1);
      res.exp = fromInteger(bias(din)) - 1;
      let x = normalize(res, { 1'b0, m, 1'b0 });
      res = tpl_1(x);
      exc = tpl_3(x);
      let y = round(defaultValue, res, tpl_2(x));
      res = tpl_1(y);
      exc = tpl_2(y);
   end
   return tuple2(res,exc);
endfunction

////////////////////////////////////////////////////////////////////////////////
/// Real type conversion
////////////////////////////////////////////////////////////////////////////////
instance RealLiteral#( FloatingPoint#(e,m) );
   function FloatingPoint#(e,m) fromReal( Real n );
      FloatingPoint#(e,m) out = defaultValue;
      Bit#(m) sfdm = 0; Bit#(2) rnd = 0; Bit#(53) rest = 0;

      let {s,ma,ex} = decodeReal(n);

      Bit#(53) sfd = s ? fromInteger(ma) : fromInteger(-ma);
      let msbindex = findIndexOneMSB_(sfd);
      let exp      = ex + msbindex - 1;

      if (msbindex == 0) begin
	 out.sign   = !s;
	 out.exp    = 0;
	 out.sfd    = 0;
      end
      else if (exp > maxexp(out)) begin
      	 out = error("Specified Real '" + realToString(n) + "' caused overflow and cannot be represented by the given type 'FloatingPoint#(" + integerToString(valueof(e)) + "," + integerToString(valueof(m)) + ")'.", out);
      end
      else if (exp < minexp_subnormal(out)) begin
      	 out = error("Specified Real '" + realToString(n) + "' caused underflow and cannot be represented by the given type 'FloatingPoint#(" + integerToString(valueof(e)) + "," + integerToString(valueof(m)) + ")'.", out);
      end
      else if (exp < minexp(out)) begin
	 out.sign       = !s;
	 out.exp        = 0;
	 { sfdm, rnd, rest } = unpack(cExtendLSB(sfd) >> (minexp(out) - exp - 1));
	 out.sfd        = sfdm;
      end
      else begin
      	 out.sign       = !s;
      	 Bit#(e) x      = fromInteger(exp) + fromInteger(bias(out));
      	 out.exp        = unpack(x);
	 { sfdm, rnd, rest } = unpack(cExtendLSB(sfd) << (53 - (msbindex - 1)));
	 out.sfd        = sfdm;
      end

      return out;
   endfunction
endinstance

////////////////////////////////////////////////////////////////////////////////
/// Literal
////////////////////////////////////////////////////////////////////////////////
instance Literal#( FloatingPoint#(e,m) );
   function FloatingPoint#(e,m) fromInteger( Integer n );
      FloatingPoint#(e,m) out = defaultValue;
      Bool issue_warning = False;
      String warning_msg = "";

      let maxsfd = 2 ** (valueof(m)+1);

      out.sign = n < 0;
      Integer x = (out.sign) ? -n : n;
      Integer exp = 0;

      if (n != 0) begin
	 // determine the initial exponent
	 while(mod(x,2) == 0 ) begin
	    exp = exp + 1;
	    x   = x / 2;
	 end

	 // determineif we have to represent too many bits -- if so, truncate
	 // perhaps warn about the loss of precision
	 if (x > maxsfd) begin
	    while(x > maxsfd) begin
	       exp = exp + 1;
	       x   = x / 2;
	    end

	    Integer s = x * (2 ** exp);
	    s = (out.sign) ? -s : s;

	    warning_msg = "Converting from Literal '" + integerToString(n) + "' to type 'FloatingPoint#(" + integerToString(valueof(e)) + "," + integerToString(valueof(m)) + ")' exceeds the precision offered.  Replacing with " + integerToString(s) + ".";
	    issue_warning = True;
	 end

	 // move the significand into a field with hidden bit explicit.
	 Bit#(TAdd#(m,1)) sx = fromInteger(x);

	 // If the hidden bit is indeed set, we are done.  Convert to float.
	 if (msb(sx) == 1) begin
	    out.exp  = fromInteger(exp + bias(out) + valueof(m));
	    out.sfd  = cExtend(sx);
	 end
	 else begin
	    Bit#(m) mval = cExtend(sx);
	    let msbindex = findIndexOneMSB_(mval);
	    out.exp      = fromInteger(exp + bias(out) + msbindex - 1);
	    out.sfd      = mval << (valueof(m) - (msbindex - 1));
	 end
      end

      return (issue_warning) ? warning(warning_msg,out) : out;
   endfunction

   function Bool inLiteralRange(FloatingPoint#(e,m) a, Integer n);
      return False;
   endfunction
endinstance


////////////////////////////////////////////////////////////////////////////////
/// Ord (sort of)
/// values are not totally ordered so some comparisons return unordered
////////////////////////////////////////////////////////////////////////////////
function Disorder compareFP( FloatingPoint#(e,m) x, FloatingPoint#(e,m) y );
   if (isNaN(x) || isNaN(y))
      return UO;
   else if (isZero(x) && isZero(y))
      return EQ;
   else begin
      let expLT  = x.exp < y.exp;
      let expEQ  = x.exp == y.exp;
      let expGT  = x.exp > y.exp;
      let sfdLT  = x.sfd < y.sfd;
      let sfdGT  = x.sfd > y.sfd;
      let sfdEQ  = x.sfd == y.sfd;

      if (x.sign && !y.sign) begin
	 return LT;
      end
      else if (!x.sign && y.sign) begin
	 return GT;
      end
      else if (!x.sign) begin
	 // both positive
	 if (expLT || (expEQ && sfdLT)) begin
	    return LT;
	 end
	 else if (expGT || (expEQ && sfdGT)) begin
	    return GT;
	 end
	 else begin
	    return EQ;
	 end
      end
      else begin
	 // both negative
	 if (expGT || (expEQ && sfdGT)) begin
	    return LT;
	 end
	 else if (expLT || (expEQ && sfdLT)) begin
	    return GT;
	 end
	 else begin
	    return EQ;
	 end
      end
   end
endfunction


instance Ord#(FloatingPoint#(e,m));
   function Bool \< ( FloatingPoint#(e,m) in1, FloatingPoint#(e,m) in2 );
      let c = compare(in1, in2);
      return (c == LT);
   endfunction

   function Bool \<= ( FloatingPoint#(e,m) in1, FloatingPoint#(e,m) in2 );
      let c = compare(in1, in2);
      return (c == LT) || (c == EQ);
   endfunction

   function Bool \> ( FloatingPoint#(e,m) in1, FloatingPoint#(e,m) in2 );
      let c = compare(in1, in2);
      return (c == GT);
   endfunction

   function Bool \>= ( FloatingPoint#(e,m) in1, FloatingPoint#(e,m) in2 );
      let c = compare(in1, in2);
      return (c == GT) || (c == EQ);
   endfunction

   function Ordering compare( FloatingPoint#(e,m) x, FloatingPoint#(e,m) y );
      let c = compareFP(x, y);
      case (c)
	 UO: return error("Unordered comparison of type " + quote("FloatingPoint") + ".");
	 EQ: return EQ;
	 LT: return LT;
	 GT: return GT;
      endcase
   endfunction

   function FloatingPoint#(e,m) min( FloatingPoint#(e,m) x, FloatingPoint#(e,m) y );
      if (isSNaN(x)) return nanQuiet(x);
      else if (isSNaN(y)) return nanQuiet(y);
      else if (isQNaN(x)) return x;
      else if (isQNaN(y)) return y;
      else begin
	 let signLT = (x.sign && !y.sign);
	 let signEQ = x.sign == y.sign;
	 let expLT  = x.exp < y.exp;
	 let expEQ  = x.exp == y.exp;
	 let manLT  = x.sfd < y.sfd;

	 if (signLT || (signEQ && expLT) || (signEQ && expEQ && manLT)) return x;
	 else return y;
      end
   endfunction

   function FloatingPoint#(e,m) max( FloatingPoint#(e,m) x, FloatingPoint#(e,m) y );
      if (isSNaN(x)) return nanQuiet(x);
      else if (isSNaN(y)) return nanQuiet(y);
      else if (isQNaN(x)) return x;
      else if (isQNaN(y)) return y;
      else begin
	 let signEQ = x.sign == y.sign;
	 let signGT = (!x.sign && y.sign);
	 let expEQ  = x.exp == y.exp;
	 let expGT  = x.exp > y.exp;
	 let manGT  = x.sfd > y.sfd;

	 if (signGT || (signEQ && expGT) || (signEQ && expEQ && manGT)) return x;
	 else return y;
      end
   endfunction
endinstance


////////////////////////////////////////////////////////////////////////////////
/// Arith (sort of)
/// but some operations are not defined
/// relationships between operations does not always hold due to NaN
////////////////////////////////////////////////////////////////////////////////
instance Arith#(FloatingPoint#(e,m))
   provisos(
      // per request of bsc
      Add#(a__, TLog#(TAdd#(1, TAdd#(TAdd#(m, 1), TAdd#(m, 1)))), TAdd#(e, 1)),
      Add#(b__, TLog#(TAdd#(1, TAdd#(m, 4))), TAdd#(e, 1)),
      Add#(c__, TLog#(TAdd#(1, TAdd#(m, 2))), TAdd#(e, 1)),
      Add#(d__, TLog#(TAdd#(1, TAdd#(TAdd#(m, 5), 1))), TAdd#(e, 1)),
      Add#(e__, TLog#(TAdd#(1, TAdd#(m, 1))), TAdd#(TAdd#(e, 1), 1)),
      Add#(f__, TLog#(TAdd#(1, TAdd#(m, 5))), TAdd#(e, 1))
      );

   function FloatingPoint#(e,m) \+ ( FloatingPoint#(e,m) in1, FloatingPoint#(e,m) in2 );
      match {.out,.exc} = addFP(in1, in2, defaultValue);
      return out;
   endfunction

   function FloatingPoint#(e,m) \- ( FloatingPoint#(e,m) in1, FloatingPoint#(e,m) in2 );
      match {.out,.exc} = addFP(in1, negate(in2), defaultValue);
      return out;
   endfunction

   function FloatingPoint#(e,m) negate (FloatingPoint#(e,m) in1 );
      in1.sign = !in1.sign;
      return in1;
   endfunction

   function FloatingPoint#(e,m) \* ( FloatingPoint#(e,m) in1, FloatingPoint#(e,m) in2 );
      match {.out,.exc} = multFP(in1, in2, defaultValue);
      return out;
   endfunction

   function FloatingPoint#(e,m) \/ ( FloatingPoint#(e,m) in1, FloatingPoint#(e,m) in2 );
      match {.out,.exc} = divFP(in1, in2, RoundMode'(defaultValue));
      return out;
   endfunction

   function FloatingPoint#(e,m) \% ( FloatingPoint#(e,m) in1, FloatingPoint#(e,m) in2 );
      return error("The operator " + quote("%") +
		   " is not defined for " + quote("FloatingPoint") + ".");
   endfunction

   function FloatingPoint#(e,m) abs (FloatingPoint#(e,m) in1 );
      in1.sign = False;
      return in1;
   endfunction

   function FloatingPoint#(e,m) signum (FloatingPoint#(e,m) in1 );
      FloatingPoint#(e,m) out = defaultValue;
      out.sign       = in1.sign;
      out.exp        = fromInteger(bias(in1));
      return out;
   endfunction

   function FloatingPoint#(e,m) \** ( FloatingPoint#(e,m) in1, FloatingPoint#(e,m) in2 );
      return error("The operator " + quote("**") +
		   " is not defined for " + quote("FloatingPoint") + ".");
   endfunction

   function FloatingPoint#(e,m) exp_e ( FloatingPoint#(e,m) in1 );
      return error("The operator " + quote("exp_e") +
		   " is not defined for " + quote("FloatingPoint") + ".");
   endfunction

   function FloatingPoint#(e,m) log ( FloatingPoint#(e,m) in1 );
      return error("The operator " + quote("log") +
                  " is not defined for " + quote("FloatingPoint") + ".");
   endfunction

   function FloatingPoint#(e,m) logb ( FloatingPoint#(e,m) in1, FloatingPoint#(e,m) in2 );
      return error("The operator " + quote("logb") +
                  " is not defined for " + quote("FloatingPoint") + ".");
   endfunction

   function FloatingPoint#(e,m) log2 ( FloatingPoint#(e,m) in1 );
      return error("The operator " + quote("log2") +
                  " is not defined for " + quote("FloatingPoint") + ".");
   endfunction

   function FloatingPoint#(e,m) log10 ( FloatingPoint#(e,m) in1 );
      return error("The operator " + quote("log10") +
                  " is not defined for " + quote("FloatingPoint") + ".");
   endfunction
endinstance

////////////////////////////////////////////////////////////////////////////////
/// Addition/Subtraction
////////////////////////////////////////////////////////////////////////////////
function Tuple2#(FloatingPoint#(e,m),Exception) addFP ( FloatingPoint#(e,m) in1, FloatingPoint#(e,m) in2, RoundMode rmode )
   provisos(
      // per request of bsc
      Add#(a__, TLog#(TAdd#(1, TAdd#(m, 5))), TAdd#(e, 1))
      );

   function Tuple7#(CommonState#(e,m),
		    Bit#(TAdd#(m,5)),
		    Bit#(TAdd#(m,5)),
		    Bool,
		    Bool,
		    Bit#(e),
		    Bit#(e)) s1_stage(Tuple3#(FloatingPoint#(e,m),
					      FloatingPoint#(e,m),
					      RoundMode) op);

      match { .opA, .opB, .rmode } = op;

      CommonState#(e,m) s = CommonState {
	 res: tagged Invalid,
	 exc: defaultValue,
	 rmode: rmode
	 };

      Int#(TAdd#(e,2)) expA = isSubNormal(opA) ? fromInteger(minexp(opA)) : signExtend(unpack(unbias(opA)));
      Int#(TAdd#(e,2)) expB = isSubNormal(opB) ? fromInteger(minexp(opB)) : signExtend(unpack(unbias(opB)));

      Bit#(TAdd#(m,5)) sfdA = {1'b0, getHiddenBit(opA), opA.sfd, 3'b0};
      Bit#(TAdd#(m,5)) sfdB = {1'b0, getHiddenBit(opB), opB.sfd, 3'b0};

      Bit#(TAdd#(m,5)) x;
      Bit#(TAdd#(m,5)) y;
      Bool sgn;
      Bool sub;
      Bit#(e) exp;
      Bit#(e) expdiff;

      if ((expB > expA) || ((expB == expA) && (sfdB > sfdA))) begin
	 exp = opB.exp;
	 expdiff = truncate(pack(expB - expA));
	 x = sfdB;
	 y = sfdA;
	 sgn = opB.sign;
	 sub = (opB.sign != opA.sign);
      end
      else begin
	 exp = opA.exp;
	 expdiff = truncate(pack(expA - expB));
	 x = sfdA;
	 y = sfdB;
	 sgn = opA.sign;
	 sub = (opA.sign != opB.sign);
      end

      if (isSNaN(opA)) begin
	 s.res = tagged Valid nanQuiet(opA);
	 s.exc.invalid_op = True;
      end
      else if (isSNaN(opB)) begin
	 s.res = tagged Valid nanQuiet(opB);
	 s.exc.invalid_op = True;
      end
      else if (isQNaN(opA)) begin
	 s.res = tagged Valid opA;
      end
      else if (isQNaN(opB)) begin
	 s.res = tagged Valid opB;
      end
      else if (isInfinity(opA) && isInfinity(opB)) begin
	 if (opA.sign == opB.sign)
	    s.res = tagged Valid infinity(opA.sign);
	 else begin
	    s.res = tagged Valid qnan();
	    s.exc.invalid_op = True;
	 end
      end
      else if (isInfinity(opA)) begin
	 s.res = tagged Valid opA;
      end
      else if (isInfinity(opB)) begin
	 s.res = tagged Valid opB;
      end

      return tuple7(s,
		    x,
		    y,
		    sgn,
		    sub,
		    exp,
		    expdiff);
   endfunction

   function Tuple6#(CommonState#(e,m),
		    Bit#(TAdd#(m,5)),
		    Bit#(TAdd#(m,5)),
		    Bool,
		    Bool,
		    Bit#(e)) s2_stage(Tuple7#(CommonState#(e,m),
					      Bit#(TAdd#(m,5)),
					      Bit#(TAdd#(m,5)),
					      Bool,
					      Bool,
					      Bit#(e),
					      Bit#(e)) op);

      match {.s, .opA, .opB, .sign, .subtract, .exp, .diff} = op;

      if (s.res matches tagged Invalid) begin
	 if (diff < fromInteger(valueOf(m) + 5)) begin
	    Bit#(TAdd#(m,5)) guard = opB;

	    guard = opB << (fromInteger(valueOf(m) + 5) - diff);
	    opB = opB >> diff;
	    opB[0] = opB[0] | (|guard);
	 end
	 else if (|opB == 1) begin
	    opB = 1;
	 end
      end

      return tuple6(s,
		    opA,
		    opB,
		    sign,
		    subtract,
		    exp);
   endfunction

   function Tuple6#(CommonState#(e,m),
		    Bit#(TAdd#(m,5)),
		    Bit#(TAdd#(m,5)),
		    Bool,
		    Bool,
		    Bit#(e)) s3_stage(Tuple6#(CommonState#(e,m),
					      Bit#(TAdd#(m,5)),
					      Bit#(TAdd#(m,5)),
					      Bool,
					      Bool,
					      Bit#(e)) op);

      match {.s, .a, .b, .sign, .subtract, .exp} = op;

      let sum = a + b;
      let diff = a - b;

      return tuple6(s,
		    sum,
		    diff,
		    sign,
		    subtract,
		    exp);
   endfunction

   function Tuple4#(CommonState#(e,m),
		    FloatingPoint#(e,m),
		    Bit#(2),
		    Bool) s4_stage(Tuple6#(CommonState#(e,m),
					   Bit#(TAdd#(m,5)),
					   Bit#(TAdd#(m,5)),
					   Bool,
					   Bool,
					   Bit#(e)) op);

      match {.s, .addres, .subres, .sign, .subtract, .exp} = op;

      FloatingPoint#(e,m) out = defaultValue;
      Bit#(2) guard = 0;

      if (s.res matches tagged Invalid) begin
	 Bit#(TAdd#(m,5)) result;

	 if (subtract) begin
	    result = subres;
	 end
	 else begin
            result = addres;
	 end

	 out.sign = sign;
	 out.exp = exp;

	 // $display("out = ", fshow(out));
	 // $display("result = 'h%x", result);
	 // $display("zeros = %d", countZerosMSB(result));

	 let y = normalize(out, result);
	 out = tpl_1(y);
	 guard = tpl_2(y);
	 s.exc = s.exc | tpl_3(y);
      end

      return tuple4(s,
		    out,
		    guard,
		    subtract);
   endfunction

   function Tuple2#(FloatingPoint#(e,m),
		    Exception) s5_stage(Tuple4#(CommonState#(e,m),
						FloatingPoint#(e,m),
						Bit#(2),
						Bool) op);

      match {.s, .rnd, .guard, .subtract} = op;

      FloatingPoint#(e,m) out = rnd;

      if (s.res matches tagged Valid .x) begin
	 out = x;
      end
      else begin
	 let y = round(s.rmode, out, guard);
	 out = tpl_1(y);
	 s.exc = s.exc | tpl_2(y);
      end

      // adjust sign for exact zero result
      if (isZero(out) && !s.exc.inexact && subtract) begin
	 out.sign = (s.rmode == Rnd_Minus_Inf);
      end

      return tuple2(out,s.exc);
   endfunction

   return s5_stage( s4_stage( s3_stage( s2_stage( s1_stage(tuple3(in1,in2,rmode)) ) ) ) );
endfunction

////////////////////////////////////////////////////////////////////////////////
/// Multiply
////////////////////////////////////////////////////////////////////////////////
function Tuple2#(FloatingPoint#(e,m),Exception) multFP ( FloatingPoint#(e,m) in1, FloatingPoint#(e,m) in2, RoundMode rmode )
   provisos(
      // per request of bsc
      Add#(a__, TLog#(TAdd#(1, TAdd#(TAdd#(m, 1), TAdd#(m, 1)))), TAdd#(e, 1))
      );

   function Tuple5#(CommonState#(e,m),
		    Bit#(TAdd#(m,1)),
		    Bit#(TAdd#(m,1)),
		    Int#(TAdd#(e,2)),
		    Bool) s1_stage(Tuple3#(FloatingPoint#(e,m),
					   FloatingPoint#(e,m),
					   RoundMode) op);

      match { .opA, .opB, .rmode } = op;

      CommonState#(e,m) s = CommonState {
	 res: tagged Invalid,
	 exc: defaultValue,
	 rmode: rmode
	 };

      Int#(TAdd#(e,2)) expA = isSubNormal(opA) ? fromInteger(minexp(opA)) : signExtend(unpack(unbias(opA)));
      Int#(TAdd#(e,2)) expB = isSubNormal(opB) ? fromInteger(minexp(opB)) : signExtend(unpack(unbias(opB)));
      Int#(TAdd#(e,2)) newexp = expA + expB;

      Bool sign = (opA.sign != opB.sign);

      Bit#(TAdd#(m,1)) opAsfd = { getHiddenBit(opA), opA.sfd };
      Bit#(TAdd#(m,1)) opBsfd = { getHiddenBit(opB), opB.sfd };

      if (isSNaN(opA)) begin
	 s.res = tagged Valid nanQuiet(opA);
	 s.exc.invalid_op = True;
      end
      else if (isSNaN(opB)) begin
	 s.res = tagged Valid nanQuiet(opB);
	 s.exc.invalid_op = True;
      end
      else if (isQNaN(opA)) begin
	 s.res = tagged Valid opA;
      end
      else if (isQNaN(opB)) begin
	 s.res = tagged Valid opB;
      end
      else if ((isInfinity(opA) && isZero(opB)) || (isZero(opA) && isInfinity(opB))) begin
	 s.res = tagged Valid qnan();
	 s.exc.invalid_op = True;
      end
      else if (isInfinity(opA) || isInfinity(opB)) begin
	 s.res = tagged Valid infinity(opA.sign != opB.sign);
      end
      else if (isZero(opA) || isZero(opB)) begin
	 s.res = tagged Valid zero(opA.sign != opB.sign);
      end
      else if (newexp > fromInteger(maxexp(opA))) begin
	 FloatingPoint#(e,m) out;
	 out.sign = (opA.sign != opB.sign);
	 out.exp = maxBound - 1;
	 out.sfd = maxBound;

	 s.exc.overflow = True;
	 s.exc.inexact = True;

	 let y = round(rmode, out, '1);
	 s.res = tagged Valid tpl_1(y);
	 s.exc = s.exc | tpl_2(y);
      end
      else if (newexp < (fromInteger(minexp_subnormal(opA))-2)) begin
	 FloatingPoint#(e,m) out;
	 out.sign = (opA.sign != opB.sign);
	 out.exp = 0;
	 out.sfd = 0;

	 s.exc.underflow = True;
	 s.exc.inexact = True;

	 let y = round(rmode, out, 'b01);
	 s.res = tagged Valid tpl_1(y);
	 s.exc = s.exc | tpl_2(y);
      end

      return tuple5(s,
		    opAsfd,
		    opBsfd,
		    newexp,
		    sign);
   endfunction

   function Tuple4#(CommonState#(e,m),
		    Bit#(TAdd#(TAdd#(m,1),TAdd#(m,1))),
		    Int#(TAdd#(e,2)),
		    Bool) s2_stage(Tuple5#(CommonState#(e,m),
					   Bit#(TAdd#(m,1)),
					   Bit#(TAdd#(m,1)),
					   Int#(TAdd#(e,2)),
					   Bool) op);

      match {.s, .opAsfd, .opBsfd, .exp, .sign} = op;

      Bit#(TAdd#(TAdd#(m,1),TAdd#(m,1))) sfdres = primMul(opAsfd, opBsfd);

      return tuple4(s,
		    sfdres,
		    exp,
		    sign);
   endfunction

   function Tuple4#(CommonState#(e,m),
		    Bit#(TAdd#(TAdd#(m,1),TAdd#(m,1))),
		    Int#(TAdd#(e,2)),
		    Bool) s3_stage(Tuple4#(CommonState#(e,m),
					   Bit#(TAdd#(TAdd#(m,1),TAdd#(m,1))),
					   Int#(TAdd#(e,2)),
					   Bool) op);
      return op;
   endfunction

   function Tuple3#(CommonState#(e,m),
		    FloatingPoint#(e,m),
		    Bit#(2)) s4_stage(Tuple4#(CommonState#(e,m),
					      Bit#(TAdd#(TAdd#(m,1),TAdd#(m,1))),
					      Int#(TAdd#(e,2)),
					      Bool) op);

      match {.s, .sfdres, .exp, .sign} = op;

      FloatingPoint#(e,m) result = defaultValue;
      Bit#(2) guard = ?;

      if (s.res matches tagged Invalid) begin
	 //$display("sfdres = 'h%x", sfdres);

	 let shift = fromInteger(minexp(result)) - exp;
	 if (shift > 0) begin
	    // subnormal
	    Bit#(1) sfdlsb = |(sfdres << (fromInteger(valueOf(TAdd#(TAdd#(m,1),TAdd#(m,1)))) - shift));

	    //$display("sfdlsb = |'h%x = 'b%b", (sfdres << (fromInteger(valueOf(TAdd#(TAdd#(m,1),TAdd#(m,1)))) - shift)), sfdlsb);

            sfdres = sfdres >> shift;
            sfdres[0] = sfdres[0] | sfdlsb;

	    result.exp = 0;
	 end
	 else begin
	    result.exp = cExtend(exp + fromInteger(bias(result)));
	 end

	 // $display("shift = %d", shift);
	 // $display("sfdres = 'h%x", sfdres);
	 // $display("result = ", fshow(result));
	 // $display("exc = 'b%b", pack(exc));
	 // $display("zeros = %d", countZerosMSB(sfdres));

	 result.sign = sign;
	 let y = normalize(result, sfdres);
	 result = tpl_1(y);
	 guard = tpl_2(y);
	 s.exc = s.exc | tpl_3(y);

	 // $display("result = ", fshow(result));
	 // $display("exc = 'b%b", pack(exc));
      end

      return tuple3(s,
		    result,
		    guard);
   endfunction

   function Tuple2#(FloatingPoint#(e,m),
		    Exception) s5_stage(Tuple3#(CommonState#(e,m),
						FloatingPoint#(e,m),
						Bit#(2)) op);

      match {.s, .rnd, .guard} = op;

      FloatingPoint#(e,m) out = rnd;

      if (s.res matches tagged Valid .x)
	 out = x;
      else begin
	 let y = round(s.rmode, out, guard);
	 out = tpl_1(y);
	 s.exc = s.exc | tpl_2(y);
      end

      return tuple2(out,s.exc);
   endfunction

   return s5_stage( s4_stage( s3_stage( s2_stage( s1_stage(tuple3(in1,in2,rmode)) ) ) ) );
endfunction

////////////////////////////////////////////////////////////////////////////////
/// Divide
////////////////////////////////////////////////////////////////////////////////
function Tuple2#(FloatingPoint#(e,m),Exception) divFP ( FloatingPoint#(e,m) in1, FloatingPoint#(e,m) in2, RoundMode rmode )
   provisos(
      Add#(e,1,ebits),
      Add#(ebits,1,ebits1),
      Add#(m,1,m1bits),
      Add#(m,5,dbits),
      Add#(dbits,1,dbits1),
      Add#(dbits,dbits,nbits),
      // per request of bsc
      Add#(a__, TLog#(TAdd#(1, dbits1)), TAdd#(e, 1)),
      Add#(m, b__, dbits1),
      Add#(2, c__, dbits1),
      Add#(d__, TLog#(TAdd#(1, TAdd#(TAdd#(m, 5), 1))), TAdd#(e, 1)),
      Add#(e__, e, ebits1),
      Add#(f__, TLog#(TAdd#(1, m1bits)), ebits1)
     );

   function Tuple7#(Maybe#(FloatingPoint#(e,m)),
		    Exception,
		    RoundMode,
		    FloatingPoint#(e,m),
		    Bit#(nbits),
		    Bit#(dbits),
		    Bit#(e)) s1_stage(Tuple3#(FloatingPoint#(e,m),
					      FloatingPoint#(e,m),
					      RoundMode) op);

      match {.in1, .in2, .rmode} = op;
      Maybe#(FloatingPoint#(e,m)) out = tagged Invalid;
      Exception exc = defaultValue;
      FloatingPoint#(e,m) result = defaultValue;
      Bit#(m1bits) sfdA = {getHiddenBit(in1), in1.sfd};
      Bit#(m1bits) sfdB = {getHiddenBit(in2), in2.sfd};
      Bit#(e) shift = 0;

      let zerosA = countZerosMSB(sfdA);
      sfdA = sfdA << zerosA;

      let zerosB = countZerosMSB(sfdB);
      sfdB = sfdB << zerosB;

      // calculate the new exponent
      Int#(ebits1) exp1 = isSubNormal(in1) ? fromInteger(minexp(in1)) : signExtend(unpack(unbias(in1)));
      Int#(ebits1) exp2 = isSubNormal(in2) ? fromInteger(minexp(in2)) : signExtend(unpack(unbias(in2)));
      Int#(ebits1) newexp = (exp1 - zeroExtend(unpack(pack(zerosA)))) - (exp2 - zeroExtend(unpack(pack(zerosB))));

      Bit#(nbits) opA = zExtendLSB({ 1'b0, sfdA });
      Bit#(dbits) opB = zExtend({ sfdB, 4'b0000 });

      // calculate the sign
      result.sign = in1.sign != in2.sign;

      if (isSNaN(in1)) begin
	 out = tagged Valid nanQuiet(in1);
	 exc.invalid_op = True;
      end
      else if (isSNaN(in2)) begin
	 out = tagged Valid nanQuiet(in2);
	 exc.invalid_op = True;
      end
      else if (isQNaN(in1)) begin
	 out = tagged Valid in1;
      end
      else if (isQNaN(in2)) begin
	 out = tagged Valid in2;
      end
      else if ((isInfinity(in1) && isInfinity(in2)) || (isZero(in1) && isZero(in2))) begin
	 out = tagged Valid qnan();
	 exc.invalid_op = True;
      end
      else if (isZero(in2) && !isInfinity(in1)) begin
	 out = tagged Valid infinity(result.sign);
	 exc.divide_0 = True;
      end
      else if (isInfinity(in1)) begin
	 out = tagged Valid infinity(result.sign);
      end
      else if (isZero(in1) || isInfinity(in2)) begin
	 out = tagged Valid zero(result.sign);
      end
      else if (newexp > fromInteger(maxexp(in1)+1)) begin
	 result.exp = maxBound - 1;
	 result.sfd = maxBound;

	 exc.overflow = True;
	 exc.inexact = True;

	 let y = round(rmode, result, '1);
	 out = tagged Valid tpl_1(y);
	 exc = exc | tpl_2(y);
      end
      else if (newexp < (fromInteger(minexp_subnormal(in1))-2)) begin
	 result.exp = 0;
	 result.sfd = 0;

	 exc.underflow = True;
	 exc.inexact = True;

	 let y = round(rmode, result, 'b01);
	 out = tagged Valid tpl_1(y);
	 exc = exc | tpl_2(y);
      end
      else if (newexp < fromInteger(minexp(result))) begin
	 result.exp = 0;
	 shift = cExtend(fromInteger(minexp(result)) - newexp);
      end
      else begin
	 result.exp = cExtend(newexp + fromInteger(bias(result)));
      end

      return tuple7(out,exc,rmode,result,opA,opB,shift);
   endfunction

   function Tuple5#(Maybe#(FloatingPoint#(e,m)),
		    Exception,
		    RoundMode,
		    FloatingPoint#(e,m),
                    Bit#(dbits1)) s3_stage(Tuple7#(Maybe#(FloatingPoint#(e,m)),
						   Exception,
						   RoundMode,
						   FloatingPoint#(e,m),
						   Bit#(nbits),
						   Bit#(dbits),
						   Bit#(e)) op);

      match {.out,.exc,.rmode,.result,.opA,.opB,.shift} = op;

      Bit#(dbits1) rsfd = ?;

      if (out matches tagged Invalid) begin
	 UInt#(dbits) q = truncate(unpack(opA) / extend(unpack(opB)));
	 UInt#(dbits) p = truncate(unpack(opA) % extend(unpack(opB)));

	 if (shift < fromInteger(valueOf(dbits1))) begin
	    Bit#(1) sfdlsb = |(pack(q << (fromInteger(valueOf(dbits1)) - shift)));
	    rsfd = cExtend(q >> shift);
	    rsfd[0] = rsfd[0] | sfdlsb;
	 end
	 else begin
	    Bit#(1) sfdlsb = |(pack(q));
	    rsfd = 0;
	    rsfd[0] = sfdlsb;
	 end

	 if (p != 0) begin
	    rsfd[0] = 1;
	 end

	 //$display(" = %d, %d", q, p);
      end

      return tuple5(out,exc,rmode,result,rsfd);
   endfunction

   function Tuple5#(Maybe#(FloatingPoint#(e,m)),
                    Exception,
                    RoundMode,
		    FloatingPoint#(e,m),
		    Bit#(2)) s4_stage(Tuple5#(Maybe#(FloatingPoint#(e,m)),
		                              Exception,
		                              RoundMode,
		                              FloatingPoint#(e,m),
                                              Bit#(dbits1)) op);

      match {.out,.exc,.rmode,.result,.rsfd} = op;

      Bit#(2) guard = ?;

      if (result.exp == maxBound) begin
	 if (truncateLSB(rsfd) == 2'b00) begin
	    rsfd = rsfd << 1;
	    result.exp = result.exp - 1;
	 end
	 else begin
	    result.exp = maxBound - 1;
	    result.sfd = maxBound;

	    exc.overflow = True;
	    exc.inexact = True;

	    let y = round(rmode, result, '1);
	    out = tagged Valid tpl_1(y);
	    exc = exc | tpl_2(y);
	 end
      end

      if (out matches tagged Invalid) begin
	 // $display("result = ", fshow(result));
	 // $display("rsfd = 'h%x", rsfd);
	 // $display("zeros = %d", countZerosMSB(rsfd));

	 match {.out_, .guard_, .exc_} = normalize(result, rsfd);
	 result = out_;
	 guard = guard_;
	 exc = exc | exc_;

	 // $display("result = ", fshow(result));
	 // $display("guard = 'b%b", guard);
	 // $display("exc = 'b%b", pack(exc));
      end

      return tuple5(out,exc,rmode,result,guard);
   endfunction

   function Tuple2#(FloatingPoint#(e,m),
		Exception) s5_stage(Tuple5#(Maybe#(FloatingPoint#(e,m)),
					    Exception,
					    RoundMode,
					    FloatingPoint#(e,m),
					    Bit#(2)) op);

      match {.out,.exc,.rmode,.result,.guard} = op;

      if (out matches tagged Valid .x)
	 result = x;
      else begin
	 match {.out_, .exc_} = round(rmode,result,guard);
	 result = out_;
	 exc = exc | exc_;
      end

      return tuple2(result,exc);
   endfunction

   return s5_stage( s4_stage( s3_stage( s1_stage(tuple3(in1,in2,rmode)) ) ) );
endfunction

////////////////////////////////////////////////////////////////////////////////
/// Square root
////////////////////////////////////////////////////////////////////////////////
function Tuple2#(FloatingPoint#(e,m),Exception) sqrtFP (FloatingPoint#(e,m) in1, RoundMode rmode)
   provisos(
      Div#(m,2,mh),
      Add#(mh,2,mh1),
      Mul#(mh1,2,nsfd),
      // per request of bsc
      Add#(1, a__, m),
      Add#(b__, TLog#(TAdd#(1, TAdd#(3, m))), TAdd#(e, 1)),
      Add#(c__, 2, TMul#(nsfd, 2)),
      Add#(1, d__, TMul#(nsfd, 2)),
      Add#(m, e__, TMul#(nsfd, 2)),
      Add#(f__, TLog#(TAdd#(1, TMul#(nsfd, 2))), TAdd#(e, 1))
      );
   FloatingPoint#(e,m) out = defaultValue;
   Exception exc = defaultValue;

   if (isSNaN(in1)) begin
      out = nanQuiet(in1);
      exc.invalid_op = True;
   end
   else if (isQNaN(in1) || isZero(in1) || (isInfinity(in1) && (in1.sign == False))) begin
      out = in1;
   end
   else if (in1.sign) begin
      out = qnan();
      exc.invalid_op = True;
   end
   else begin
      out = in1;
      Int#(e) exp = unpack(unbias(out));
      out.exp = pack(exp >> 1) + fromInteger(bias(out));

      Bit#(TMul#(nsfd,2)) sfd = zExtendLSB({1'b0,getHiddenBit(in1),in1.sfd});
      Bit#(TMul#(nsfd,2)) res = 0;
      Bit#(TMul#(nsfd,2)) bits = reverseBits(extend(2'b10));

      if ((in1.exp & 1) == 0) begin
	 out.exp = out.exp + 1;
	 sfd = sfd >> 1;
      end

      // bits is highest power of 4 less than or equal to sfd
      let s0 = countZerosMSB(sfd);
      let b0 = countZerosMSB(bits);
      if (s0 > 0) begin
	 let shift = (s0 - b0) & ~'b1;
	 bits = bits >> shift;
      end

      while (bits != 0) begin
	 let sum = res + bits;

	 if (sfd >= sum) begin
	    sfd = sfd - sum;
	    res = (res >> 1) + bits;
	 end
	 else begin
	    res = res >> 1;
	 end

	 bits = bits >> 2;
      end

      sfd = sfd << (valueOf(nsfd) - 1);

      // normalize the result
      let y = normalize(out, sfd);
      out = tpl_1(y);
      exc = tpl_3(y);

      let x = round(rmode, out, tpl_2(y));
      out = tpl_1(x);
      exc = exc | tpl_2(x);
   end

   return tuple2(out,exc);
endfunction

////////////////////////////////////////////////////////////////////////////////
/// Pipelined Floating Point Adder
////////////////////////////////////////////////////////////////////////////////
typedef struct {
   Maybe#(FloatingPoint#(e,m)) res;
   Exception exc;
   RoundMode rmode;
   } CommonState#(numeric type e, numeric type m) deriving (Bits, Eq);

module mkFloatingPointAdder(Server#(Tuple3#(FloatingPoint#(e,m), FloatingPoint#(e,m), RoundMode), Tuple2#(FloatingPoint#(e,m),Exception)))
   provisos(
      // per request of bsc
      Add#(a__, TLog#(TAdd#(1, TAdd#(m, 5))), TAdd#(e, 1))
      );

   ////////////////////////////////////////////////////////////////////////////////
   /// S0
   ////////////////////////////////////////////////////////////////////////////////
   FIFO#(Tuple3#(FloatingPoint#(e,m),
		 FloatingPoint#(e,m),
		 RoundMode))                 fOperands_S0        <- mkLFIFO;

   ////////////////////////////////////////////////////////////////////////////////
   /// S1 - subtract exponents
   ////////////////////////////////////////////////////////////////////////////////
   FIFO#(Tuple7#(CommonState#(e,m),
		 Bit#(TAdd#(m,5)),
		 Bit#(TAdd#(m,5)),
		 Bool,
		 Bool,
		 Bit#(e),
		 Bit#(e))) fState_S1 <- mkLFIFO;

   rule s1_stage;
      match { .opA, .opB, .rmode } <- toGet(fOperands_S0).get;

      CommonState#(e,m) s = CommonState {
	 res: tagged Invalid,
	 exc: defaultValue,
	 rmode: rmode
	 };

      Int#(TAdd#(e,2)) expA = isSubNormal(opA) ? fromInteger(minexp(opA)) : signExtend(unpack(unbias(opA)));
      Int#(TAdd#(e,2)) expB = isSubNormal(opB) ? fromInteger(minexp(opB)) : signExtend(unpack(unbias(opB)));

      Bit#(TAdd#(m,5)) sfdA = {1'b0, getHiddenBit(opA), opA.sfd, 3'b0};
      Bit#(TAdd#(m,5)) sfdB = {1'b0, getHiddenBit(opB), opB.sfd, 3'b0};

      Bit#(TAdd#(m,5)) x;
      Bit#(TAdd#(m,5)) y;
      Bool sgn;
      Bool sub;
      Bit#(e) exp;
      Bit#(e) expdiff;

      if ((expB > expA) || ((expB == expA) && (sfdB > sfdA))) begin
	 exp = opB.exp;
	 expdiff = truncate(pack(expB - expA));
	 x = sfdB;
	 y = sfdA;
	 sgn = opB.sign;
	 sub = (opB.sign != opA.sign);
      end
      else begin
	 exp = opA.exp;
	 expdiff = truncate(pack(expA - expB));
	 x = sfdA;
	 y = sfdB;
	 sgn = opA.sign;
	 sub = (opA.sign != opB.sign);
      end

      if (isSNaN(opA)) begin
	 s.res = tagged Valid nanQuiet(opA);
	 s.exc.invalid_op = True;
      end
      else if (isSNaN(opB)) begin
	 s.res = tagged Valid nanQuiet(opB);
	 s.exc.invalid_op = True;
      end
      else if (isQNaN(opA)) begin
	 s.res = tagged Valid opA;
      end
      else if (isQNaN(opB)) begin
	 s.res = tagged Valid opB;
      end
      else if (isInfinity(opA) && isInfinity(opB)) begin
	 if (opA.sign == opB.sign)
	    s.res = tagged Valid infinity(opA.sign);
	 else begin
	    s.res = tagged Valid qnan();
	    s.exc.invalid_op = True;
	 end
      end
      else if (isInfinity(opA)) begin
	 s.res = tagged Valid opA;
      end
      else if (isInfinity(opB)) begin
	 s.res = tagged Valid opB;
      end

      fState_S1.enq(tuple7(s,
			   x,
			   y,
			   sgn,
			   sub,
			   exp,
			   expdiff));
   endrule

   ////////////////////////////////////////////////////////////////////////////////
   /// S2 - align significands
   ////////////////////////////////////////////////////////////////////////////////
   FIFO#(Tuple6#(CommonState#(e,m),
		 Bit#(TAdd#(m,5)),
		 Bit#(TAdd#(m,5)),
		 Bool,
		 Bool,
		 Bit#(e))) fState_S2 <- mkLFIFO;

   rule s2_stage;
      match {.s, .opA, .opB, .sign, .subtract, .exp, .diff} <- toGet(fState_S1).get;

      if (s.res matches tagged Invalid) begin
	 if (diff < fromInteger(valueOf(m) + 5)) begin
	    Bit#(TAdd#(m,5)) guard = opB;

	    guard = opB << (fromInteger(valueOf(m) + 5) - diff);
	    opB = opB >> diff;
	    opB[0] = opB[0] | (|guard);
	 end
	 else if (|opB == 1) begin
	    opB = 1;
	 end
      end

      fState_S2.enq(tuple6(s,
			   opA,
			   opB,
			   sign,
			   subtract,
			   exp));
   endrule

   ////////////////////////////////////////////////////////////////////////////////
   /// S3 - add/subtract significands
   ////////////////////////////////////////////////////////////////////////////////
   FIFO#(Tuple6#(CommonState#(e,m),
		 Bit#(TAdd#(m,5)),
		 Bit#(TAdd#(m,5)),
		 Bool,
		 Bool,
		 Bit#(e))) fState_S3 <- mkLFIFO;

   rule s3_stage;
      match {.s, .a, .b, .sign, .subtract, .exp} <- toGet(fState_S2).get;

      let sum = a + b;
      let diff = a - b;

      fState_S3.enq(tuple6(s,
			   sum,
			   diff,
			   sign,
			   subtract,
			   exp));
   endrule

   ////////////////////////////////////////////////////////////////////////////////
   /// S4 - normalize
   ////////////////////////////////////////////////////////////////////////////////
   FIFO#(Tuple4#(CommonState#(e,m),
		 FloatingPoint#(e,m),
		 Bit#(2),
		 Bool)) fState_S4 <- mkLFIFO;

   rule s4_stage;
      match {.s, .addres, .subres, .sign, .subtract, .exp} <- toGet(fState_S3).get;

      FloatingPoint#(e,m) out = defaultValue;
      Bit#(2) guard = 0;

      if (s.res matches tagged Invalid) begin
	 Bit#(TAdd#(m,5)) result;

	 if (subtract) begin
	    result = subres;
	 end
	 else begin
            result = addres;
	 end

	 out.sign = sign;
	 out.exp = exp;

	 // $display("out = ", fshow(out));
	 // $display("result = 'h%x", result);
	 // $display("zeros = %d", countZerosMSB(result));

	 let y = normalize(out, result);
	 out = tpl_1(y);
	 guard = tpl_2(y);
	 s.exc = s.exc | tpl_3(y);
      end

      fState_S4.enq(tuple4(s,
			   out,
			   guard,
			   subtract));
   endrule

   ////////////////////////////////////////////////////////////////////////////////
   /// S5 - round result
   ////////////////////////////////////////////////////////////////////////////////
   FIFO#(Tuple2#(FloatingPoint#(e,m),Exception)) fResult_S5          <- mkLFIFO;

   rule s5_stage;
      match {.s, .rnd, .guard, .subtract} <- toGet(fState_S4).get;

      FloatingPoint#(e,m) out = rnd;

      if (s.res matches tagged Valid .x) begin
	 out = x;
      end
      else begin
	 let y = round(s.rmode, out, guard);
	 out = tpl_1(y);
	 s.exc = s.exc | tpl_2(y);
      end

      // adjust sign for exact zero result
      if (isZero(out) && !s.exc.inexact && subtract) begin
	 out.sign = (s.rmode == Rnd_Minus_Inf);
      end

      fResult_S5.enq(tuple2(out,s.exc));
   endrule

   ////////////////////////////////////////////////////////////////////////////////
   /// Interface Connections / Methods
   ////////////////////////////////////////////////////////////////////////////////
   interface request = toPut(fOperands_S0);
   interface response = toGet(fResult_S5);

endmodule: mkFloatingPointAdder

////////////////////////////////////////////////////////////////////////////////
/// Pipelined Floating Point Multiplier
////////////////////////////////////////////////////////////////////////////////
module mkFloatingPointMultiplier(Server#(Tuple3#(FloatingPoint#(e,m), FloatingPoint#(e,m), RoundMode), Tuple2#(FloatingPoint#(e,m),Exception)))
   provisos(
      // per request of bsc
      Add#(a__, TLog#(TAdd#(1, TAdd#(TAdd#(m, 1), TAdd#(m, 1)))), TAdd#(e, 1))
      );

   ////////////////////////////////////////////////////////////////////////////////
   /// S0
   ////////////////////////////////////////////////////////////////////////////////
   FIFO#(Tuple3#(FloatingPoint#(e,m),
		 FloatingPoint#(e,m),
		 RoundMode))                 fOperands_S0        <- mkLFIFO;

   ////////////////////////////////////////////////////////////////////////////////
   /// S1 - calculate the new exponent/sign
   ////////////////////////////////////////////////////////////////////////////////
   FIFO#(Tuple5#(CommonState#(e,m),
		 Bit#(TAdd#(m,1)),
		 Bit#(TAdd#(m,1)),
		 Int#(TAdd#(e,2)),
		 Bool)) fState_S1 <- mkLFIFO;

   rule s1_stage;
      match { .opA, .opB, .rmode } <- toGet(fOperands_S0).get;

      CommonState#(e,m) s = CommonState {
	 res: tagged Invalid,
	 exc: defaultValue,
	 rmode: rmode
	 };

      Int#(TAdd#(e,2)) expA = isSubNormal(opA) ? fromInteger(minexp(opA)) : signExtend(unpack(unbias(opA)));
      Int#(TAdd#(e,2)) expB = isSubNormal(opB) ? fromInteger(minexp(opB)) : signExtend(unpack(unbias(opB)));
      Int#(TAdd#(e,2)) newexp = expA + expB;

      Bool sign = (opA.sign != opB.sign);

      Bit#(TAdd#(m,1)) opAsfd = { getHiddenBit(opA), opA.sfd };
      Bit#(TAdd#(m,1)) opBsfd = { getHiddenBit(opB), opB.sfd };

      if (isSNaN(opA)) begin
	 s.res = tagged Valid nanQuiet(opA);
	 s.exc.invalid_op = True;
      end
      else if (isSNaN(opB)) begin
	 s.res = tagged Valid nanQuiet(opB);
	 s.exc.invalid_op = True;
      end
      else if (isQNaN(opA)) begin
	 s.res = tagged Valid opA;
      end
      else if (isQNaN(opB)) begin
	 s.res = tagged Valid opB;
      end
      else if ((isInfinity(opA) && isZero(opB)) || (isZero(opA) && isInfinity(opB))) begin
	 s.res = tagged Valid qnan();
	 s.exc.invalid_op = True;
      end
      else if (isInfinity(opA) || isInfinity(opB)) begin
	 s.res = tagged Valid infinity(opA.sign != opB.sign);
      end
      else if (isZero(opA) || isZero(opB)) begin
	 s.res = tagged Valid zero(opA.sign != opB.sign);
      end
      else if (newexp > fromInteger(maxexp(opA))) begin
	 FloatingPoint#(e,m) out;
	 out.sign = (opA.sign != opB.sign);
	 out.exp = maxBound - 1;
	 out.sfd = maxBound;

	 s.exc.overflow = True;
	 s.exc.inexact = True;

	 let y = round(rmode, out, '1);
	 s.res = tagged Valid tpl_1(y);
	 s.exc = s.exc | tpl_2(y);
      end
      else if (newexp < (fromInteger(minexp_subnormal(opA))-2)) begin
	 FloatingPoint#(e,m) out;
	 out.sign = (opA.sign != opB.sign);
	 out.exp = 0;
	 out.sfd = 0;

	 s.exc.underflow = True;
	 s.exc.inexact = True;

	 let y = round(rmode, out, 'b01);
	 s.res = tagged Valid tpl_1(y);
	 s.exc = s.exc | tpl_2(y);
      end

      fState_S1.enq(tuple5(s,
			   opAsfd,
			   opBsfd,
			   newexp,
			   sign));
   endrule

   ////////////////////////////////////////////////////////////////////////////////
   /// S2
   ////////////////////////////////////////////////////////////////////////////////
   FIFO#(Tuple4#(CommonState#(e,m),
		 Bit#(TAdd#(TAdd#(m,1),TAdd#(m,1))),
		 Int#(TAdd#(e,2)),
		 Bool)) fState_S2 <- mkLFIFO;

   rule s2_stage;
      match {.s, .opAsfd, .opBsfd, .exp, .sign} <- toGet(fState_S1).get;

      Bit#(TAdd#(TAdd#(m,1),TAdd#(m,1))) sfdres = primMul(opAsfd, opBsfd);

      fState_S2.enq(tuple4(s,
			   sfdres,
			   exp,
			   sign));
   endrule

   ////////////////////////////////////////////////////////////////////////////////
   /// S3
   ////////////////////////////////////////////////////////////////////////////////
   FIFO#(Tuple4#(CommonState#(e,m),
		 Bit#(TAdd#(TAdd#(m,1),TAdd#(m,1))),
		 Int#(TAdd#(e,2)),
		 Bool)) fState_S3 <- mkLFIFO;

   rule s3_stage;
      let x <- toGet(fState_S2).get;
      fState_S3.enq(x);
   endrule

   ////////////////////////////////////////////////////////////////////////////////
   /// S4
   ////////////////////////////////////////////////////////////////////////////////
   FIFO#(Tuple3#(CommonState#(e,m),
		 FloatingPoint#(e,m),
		 Bit#(2))) fState_S4 <- mkLFIFO;

   rule s4_stage;
      match {.s, .sfdres, .exp, .sign} <- toGet(fState_S3).get;

      FloatingPoint#(e,m) result = defaultValue;
      Bit#(2) guard = ?;

      if (s.res matches tagged Invalid) begin
	 //$display("sfdres = 'h%x", sfdres);

	 let shift = fromInteger(minexp(result)) - exp;
	 if (shift > 0) begin
	    // subnormal
	    Bit#(1) sfdlsb = |(sfdres << (fromInteger(valueOf(TAdd#(TAdd#(m,1),TAdd#(m,1)))) - shift));

	    //$display("sfdlsb = |'h%x = 'b%b", (sfdres << (fromInteger(valueOf(TAdd#(TAdd#(m,1),TAdd#(m,1)))) - shift)), sfdlsb);

            sfdres = sfdres >> shift;
            sfdres[0] = sfdres[0] | sfdlsb;

	    result.exp = 0;
	 end
	 else begin
	    result.exp = cExtend(exp + fromInteger(bias(result)));
	 end

	 // $display("shift = %d", shift);
	 // $display("sfdres = 'h%x", sfdres);
	 // $display("result = ", fshow(result));
	 // $display("exc = 'b%b", pack(exc));
	 // $display("zeros = %d", countZerosMSB(sfdres));

	 result.sign = sign;
	 let y = normalize(result, sfdres);
	 result = tpl_1(y);
	 guard = tpl_2(y);
	 s.exc = s.exc | tpl_3(y);

	 // $display("result = ", fshow(result));
	 // $display("exc = 'b%b", pack(exc));
      end

      fState_S4.enq(tuple3(s,
			   result,
			   guard));
   endrule

   ////////////////////////////////////////////////////////////////////////////////
   /// S5
   ////////////////////////////////////////////////////////////////////////////////
   FIFO#(Tuple2#(FloatingPoint#(e,m),Exception)) fResult_S5          <- mkLFIFO;

   rule s5_stage;
      match {.s, .rnd, .guard} <- toGet(fState_S4).get;

      FloatingPoint#(e,m) out = rnd;

      if (s.res matches tagged Valid .x)
	 out = x;
      else begin
	 let y = round(s.rmode, out, guard);
	 out = tpl_1(y);
	 s.exc = s.exc | tpl_2(y);
      end

      fResult_S5.enq(tuple2(out,s.exc));
   endrule

   ////////////////////////////////////////////////////////////////////////////////
   /// Interface Connections / Methods
   ////////////////////////////////////////////////////////////////////////////////
   interface request = toPut(fOperands_S0);
   interface response = toGet(fResult_S5);

endmodule: mkFloatingPointMultiplier

////////////////////////////////////////////////////////////////////////////////
/// Floating point divider
////////////////////////////////////////////////////////////////////////////////
(* options = "-aggressive-conditions" *)
module mkFloatingPointDivider#(Server#(Tuple2#(UInt#(nbits),UInt#(dbits)),Tuple2#(UInt#(dbits),UInt#(dbits))) div)(Server#(Tuple3#(FloatingPoint#(e,m), FloatingPoint#(e,m), RoundMode), Tuple2#(FloatingPoint#(e,m),Exception)))
   provisos(
      Add#(e,1,ebits),
      Add#(ebits,1,ebits1),
      Add#(m,1,m1bits),
      Add#(m,5,dbits),
      Add#(dbits,1,dbits1),
      Add#(dbits,dbits,nbits),
      // per bsc request
      Mul#(2, dbits, nbits),
      Add#(1, nbits, TAdd#(dbits, a__)),
      Add#(m, b__, dbits1),
      Add#(c__, TLog#(TAdd#(1, dbits1)), TAdd#(e, 1)),
      Add#(d__, e, ebits1),
      Add#(e__, TLog#(TAdd#(1, m1bits)), ebits1),
      Add#(2, f__, dbits),
      Add#(2, g__, dbits1)
      );
   FIFO#(Tuple3#(FloatingPoint#(e,m),
		 FloatingPoint#(e,m),
		 RoundMode))                     fOperands_S0        <- mkLFIFO;

   //Server#(Tuple2#(UInt#(nbits),UInt#(dbits)),Tuple2#(UInt#(dbits),UInt#(dbits))) div <- mkDivider(1);

   FIFO#(Tuple7#(Maybe#(FloatingPoint#(e,m)),
		 Exception,
		 RoundMode,
		 FloatingPoint#(e,m),
		 Bit#(nbits),
		 Bit#(dbits),
		 Bit#(e))) fState_S1 <- mkLFIFO;

   rule s1_stage;
      match {.in1, .in2, .rmode} <- toGet(fOperands_S0).get;
      Maybe#(FloatingPoint#(e,m)) out = tagged Invalid;
      Exception exc = defaultValue;
      FloatingPoint#(e,m) result = defaultValue;
      Bit#(m1bits) sfdA = {getHiddenBit(in1), in1.sfd};
      Bit#(m1bits) sfdB = {getHiddenBit(in2), in2.sfd};
      Bit#(e) shift = 0;

      let zerosA = countZerosMSB(sfdA);
      sfdA = sfdA << zerosA;

      let zerosB = countZerosMSB(sfdB);
      sfdB = sfdB << zerosB;

      // calculate the new exponent
      Int#(ebits1) exp1 = isSubNormal(in1) ? fromInteger(minexp(in1)) : signExtend(unpack(unbias(in1)));
      Int#(ebits1) exp2 = isSubNormal(in2) ? fromInteger(minexp(in2)) : signExtend(unpack(unbias(in2)));
      Int#(ebits1) newexp = (exp1 - zeroExtend(unpack(pack(zerosA)))) - (exp2 - zeroExtend(unpack(pack(zerosB))));

      Bit#(nbits) opA = zExtendLSB({ 1'b0, sfdA });
      Bit#(dbits) opB = zExtend({ sfdB, 4'b0000 });

      // calculate the sign
      result.sign = in1.sign != in2.sign;

      if (isSNaN(in1)) begin
	 out = tagged Valid nanQuiet(in1);
	 exc.invalid_op = True;
      end
      else if (isSNaN(in2)) begin
	 out = tagged Valid nanQuiet(in2);
	 exc.invalid_op = True;
      end
      else if (isQNaN(in1)) begin
	 out = tagged Valid in1;
      end
      else if (isQNaN(in2)) begin
	 out = tagged Valid in2;
      end
      else if ((isInfinity(in1) && isInfinity(in2)) || (isZero(in1) && isZero(in2))) begin
	 out = tagged Valid qnan();
	 exc.invalid_op = True;
      end
      else if (isZero(in2) && !isInfinity(in1)) begin
	 out = tagged Valid infinity(result.sign);
	 exc.divide_0 = True;
      end
      else if (isInfinity(in1)) begin
	 out = tagged Valid infinity(result.sign);
      end
      else if (isZero(in1) || isInfinity(in2)) begin
	 out = tagged Valid zero(result.sign);
      end
      else if (newexp > fromInteger(maxexp(in1)+1)) begin
	 result.exp = maxBound - 1;
	 result.sfd = maxBound;

	 exc.overflow = True;
	 exc.inexact = True;

	 let y = round(rmode, result, '1);
	 out = tagged Valid tpl_1(y);
	 exc = exc | tpl_2(y);
      end
      else if (newexp < (fromInteger(minexp_subnormal(in1))-2)) begin
	 result.exp = 0;
	 result.sfd = 0;

	 exc.underflow = True;
	 exc.inexact = True;

	 let y = round(rmode, result, 'b01);
	 out = tagged Valid tpl_1(y);
	 exc = exc | tpl_2(y);
      end
      else if (newexp < fromInteger(minexp(result))) begin
	 result.exp = 0;
	 shift = cExtend(fromInteger(minexp(result)) - newexp);
      end
      else begin
	 result.exp = cExtend(newexp + fromInteger(bias(result)));
      end

      fState_S1.enq(tuple7(out,exc,rmode,result,opA,opB,shift));
   endrule

   FIFO#(Tuple5#(Maybe#(FloatingPoint#(e,m)),
		 Exception,
		 RoundMode,
		 FloatingPoint#(e,m),
		 Bit#(e))) fState_S2 <- mkLFIFO;

   rule s2_stage;
      match {.out,.exc,.rmode,.result,.opA,.opB,.shift} <- toGet(fState_S1).get;

      if (out matches tagged Invalid) begin
	 //$display("%d / %d", opA, opB);
	 div.request.put(tuple2(unpack(opA),unpack(opB)));
      end

      fState_S2.enq(tuple5(out,exc,rmode,result,shift));
   endrule

   FIFO#(Tuple5#(Maybe#(FloatingPoint#(e,m)),
		 Exception,
		 RoundMode,
		 FloatingPoint#(e,m),
		 Bit#(dbits1))) fState_S3 <- mkLFIFO;

   rule s3_stage;
      match {.out,.exc,.rmode,.result,.shift} <- toGet(fState_S2).get;

      Bit#(dbits1) rsfd = ?;

      if (out matches tagged Invalid) begin
	 match {.q,.p} <- div.response.get;

	 if (shift < fromInteger(valueOf(dbits1))) begin
            UInt#(dbits1) qdbits1 = extend(q);
	    Bit#(1) sfdlsb = |(pack(qdbits1 << (fromInteger(valueOf(dbits1)) - shift)));
	    rsfd = cExtend(q >> shift);
	    rsfd[0] = rsfd[0] | sfdlsb;
	 end
	 else begin
	    Bit#(1) sfdlsb = |(pack(q));
	    rsfd = 0;
	    rsfd[0] = sfdlsb;
	 end

	 if (p != 0) begin
	    rsfd[0] = 1;
	 end

	 //$display(" = %d, %d", q, p);
      end

      fState_S3.enq(tuple5(out,exc,rmode,result,rsfd));
   endrule

   FIFO#(Tuple5#(Maybe#(FloatingPoint#(e,m)),
		 Exception,
		 RoundMode,
		 FloatingPoint#(e,m),
		 Bit#(2))) fState_S4 <- mkLFIFO;

   rule s4_stage;
      match {.out,.exc,.rmode,.result,.rsfd} <- toGet(fState_S3).get;

      Bit#(2) guard = ?;

      if (result.exp == maxBound) begin
	 if (truncateLSB(rsfd) == 2'b00) begin
	    rsfd = rsfd << 1;
	    result.exp = result.exp - 1;
	 end
	 else begin
	    result.exp = maxBound - 1;
	    result.sfd = maxBound;

	    exc.overflow = True;
	    exc.inexact = True;

	    let y = round(rmode, result, '1);
	    out = tagged Valid tpl_1(y);
	    exc = exc | tpl_2(y);
	 end
      end

      if (out matches tagged Invalid) begin
	 // $display("result = ", fshow(result));
	 // $display("rsfd = 'h%x", rsfd);
	 // $display("zeros = %d", countZerosMSB(rsfd));

	 match {.out_, .guard_, .exc_} = normalize(result, rsfd);
	 result = out_;
	 guard = guard_;
	 exc = exc | exc_;

	 // $display("result = ", fshow(result));
	 // $display("guard = 'b%b", guard);
	 // $display("exc = 'b%b", pack(exc));
      end

      fState_S4.enq(tuple5(out,exc,rmode,result,guard));
   endrule

   FIFO#(Tuple2#(FloatingPoint#(e,m),Exception)) fResult_S5          <- mkLFIFO;

   rule s5_stage;
      match {.out,.exc,.rmode,.result,.guard} <- toGet(fState_S4).get;

      if (out matches tagged Valid .x)
	 result = x;
      else begin
	 match {.out_, .exc_} = round(rmode,result,guard);
	 result = out_;
	 exc = exc | exc_;
      end

      fResult_S5.enq(tuple2(result,exc));
   endrule

   interface request = toPut(fOperands_S0);
   interface response = toGet(fResult_S5);
endmodule

////////////////////////////////////////////////////////////////////////////////
/// Floating point square root
////////////////////////////////////////////////////////////////////////////////
(* options = "-aggressive-conditions" *)
module mkFloatingPointSquareRooter#(Server#(UInt#(TMul#(2,nsfd)),Tuple2#(UInt#(TMul#(2,nsfd)),Bool)) sqrt)(Server#(Tuple2#(FloatingPoint#(e,m),RoundMode),Tuple2#(FloatingPoint#(e,m),Exception)))
   provisos(
      Div#(m,2,mh),
      Add#(mh,3,mh1),
      Mul#(mh1,2,nsfd),
      // per request of bsc
      Add#(a__, 2, nsfd),
      Log#(TAdd#(1, nsfd), TLog#(TAdd#(nsfd, 1))),
      Add#(1, b__, nsfd),
      Add#(m, c__, nsfd),
      Add#(d__, TLog#(TAdd#(1, nsfd)), TAdd#(e, 1)),
      Add#(e__, nsfd, TMul#(2, nsfd)),
      Log#(TAdd#(1, TMul#(2, nsfd)), TLog#(TAdd#(TMul#(2, nsfd), 1))),
      Add#(g__, 2, TMul#(2, nsfd)),
      Add#(f__, TAdd#(nsfd, 1), TMul#(2, nsfd)),
      Add#(m, h__, TAdd#(nsfd, 1)),
      Add#(i__, TLog#(TAdd#(1, TAdd#(nsfd, 1))), TAdd#(e, 1)),
      Add#(nsfd, TMul#(2, nsfd), j__),
      Add#(k__, TLog#(TAdd#(nsfd, 1)), e),
      Add#(l__, TLog#(TAdd#(nsfd, 1)), TAdd#(e, 2))
      );

   //Server#(UInt#(TMul#(2,nsfd)),Tuple2#(UInt#(TMul#(2,nsfd)),Bool)) sqrt <- mkSquareRooter(1);

   FIFO#(Tuple2#(FloatingPoint#(e,m),RoundMode)) fOperand_S0 <- mkLFIFO;

   FIFO#(Tuple5#(Maybe#(FloatingPoint#(e,m)),
		 Exception,
		 RoundMode,
		 FloatingPoint#(e,m),
		 Bit#(nsfd))) fState_S1 <- mkLFIFO;

   rule s1_stage;
      match {.op, .rmode} <- toGet(fOperand_S0).get;
      Exception exc = defaultValue;
      if (isSNaN(op)) begin
	 exc.invalid_op = True;
	 fState_S1.enq(tuple5(tagged Valid nanQuiet(op),exc,?,?,?));
      end
      else if (isQNaN(op) || isZero(op) || (isInfinity(op) && (op.sign == False))) begin
	 fState_S1.enq(tuple5(tagged Valid op,exc,?,?,?));
      end
      else if (op.sign) begin
	 exc.invalid_op = True;
	 fState_S1.enq(tuple5(tagged Valid qnan(),exc,?,?,?));
      end
      else begin
	 let out = op;
	 Int#(TAdd#(e,2)) exp = isSubNormal(op) ? fromInteger(minexp(op)) : signExtend(unpack(unbias(out)));
	 Bit#(nsfd) sfd = zExtendLSB({1'b0, getHiddenBit(op), op.sfd});

	 let zeros = countZerosMSB(sfd);
	 sfd = sfd << (zeros - 1);

	 exp = exp - zeroExtend(unpack(pack(zeros)));

	 out.exp = truncate(pack(exp >> 1) + fromInteger(bias(out)) + 1);

	 if ((exp & 1) == 0) begin
	    sfd = sfd >> 1;
	 end

	 fState_S1.enq(tuple5(tagged Invalid,exc,rmode,out,sfd));
      end
   endrule

   FIFO#(Tuple4#(Maybe#(FloatingPoint#(e,m)),
		 Exception,
		 RoundMode,
		 FloatingPoint#(e,m))) fState_S2 <- mkLFIFO;

   rule s2_stage;
      match {.result, .exc, .rmode, .out, .sfd} <- toGet(fState_S1).get;
      if (result matches tagged Invalid) begin
	 sqrt.request.put(unpack(zExtendLSB(sfd)));
      end
      fState_S2.enq(tuple4(result,exc,rmode,out));
   endrule

   FIFO#(Tuple5#(Maybe#(FloatingPoint#(e,m)),
		Exception,
		RoundMode,
		FloatingPoint#(e,m),
		Bit#(TAdd#(nsfd,1)))) fState_S3 <- mkLFIFO;

   rule s3_stage;
      match {.result, .exc, .rmode, .out} <- toGet(fState_S2).get;
      Bit#(TAdd#(nsfd,1)) sfd = ?;
      if (result matches tagged Invalid) begin
	 match {.s, .inexact} <- sqrt.response.get;
	 sfd = truncate(pack(s));
	 if (inexact) begin
	    sfd[0] = 1;
	 end
      end
      fState_S3.enq(tuple5(result,exc,rmode,out,sfd));
   endrule

   FIFO#(Tuple5#(Maybe#(FloatingPoint#(e,m)),
		 Exception,
		 RoundMode,
		 FloatingPoint#(e,m),
		 Bit#(2))) fState_S4 <- mkLFIFO;

   rule s4_stage;
      match {.result, .exc, .rmode, .out, .sfd} <- toGet(fState_S3).get;
      Bit#(2) guard = ?;
      if (result matches tagged Invalid) begin
	 match {.out_, .guard_, .exc_} = normalize(out, sfd);
	 out = out_;
	 guard = guard_;
	 exc = exc_;
      end
      fState_S4.enq(tuple5(result,exc,rmode,out,guard));
   endrule

   FIFO#(Tuple2#(FloatingPoint#(e,m),Exception)) fResult_S5 <- mkLFIFO;

   rule s5_stage;
      match {.result, .exc, .rmode, .out, .guard} <- toGet(fState_S4).get;
      if (result matches tagged Valid .x) begin
	 out = x;
      end
      else begin
	 match {.out_, .exc_} = round(rmode, out, guard);
	 out = out_;
	 exc = exc | exc_;
      end

      fResult_S5.enq(tuple2(out,exc));
   endrule

   interface request = toPut(fOperand_S0);
   interface response = toGet(fResult_S5);

endmodule

////////////////////////////////////////////////////////////////////////////////
/// Floating point fused multiple accumulate
////////////////////////////////////////////////////////////////////////////////
module mkFloatingPointFusedMultiplyAccumulate(Server#(Tuple4#(Maybe#(FloatingPoint#(e,m)), FloatingPoint#(e,m), FloatingPoint#(e,m), RoundMode), Tuple2#(FloatingPoint#(e,m),Exception)))
   provisos(
      Add#(e,2,ebits),
      Add#(m,1,mbits),
      Add#(m,5,m5bits),
      Add#(mbits,mbits,mmbits),
      // per request of bsc
      Add#(1, a__, mmbits),
      Add#(m, b__, mmbits),
      Add#(c__, TLog#(TAdd#(1, mmbits)), TAdd#(e, 1)),
      Add#(d__, TLog#(TAdd#(1, m5bits)), TAdd#(e, 1)),
      Add#(1, TAdd#(1, TAdd#(m, 3)), m5bits)
      );

   FIFO#(Tuple4#(Maybe#(FloatingPoint#(e,m)),
		 FloatingPoint#(e,m),
		 FloatingPoint#(e,m),
		 RoundMode)) fOperand_S0 <- mkLFIFO;

   FIFO#(Tuple7#(CommonState#(e,m),
		 Bool,
		 FloatingPoint#(e,m),
		 Bool,
		 Int#(ebits),
		 Bit#(mbits),
		 Bit#(mbits))) fState_S1 <- mkLFIFO;

   // check operands, compute exponent for multiply
   rule s1_stage;
      match { .mopA, .opB, .opC, .rmode } <- toGet(fOperand_S0).get;

      CommonState#(e,m) s = CommonState {
	 res: tagged Invalid,
	 exc: defaultValue,
	 rmode: rmode
	 };

      Bool acc = False;
      FloatingPoint#(e,m) opA = 0;

      if (mopA matches tagged Valid .opA_) begin
	 opA = opA_;
	 acc = True;
      end

      Int#(ebits) expB = isSubNormal(opB) ? fromInteger(minexp(opB)) : signExtend(unpack(unbias(opB)));
      Int#(ebits) expC = isSubNormal(opC) ? fromInteger(minexp(opC)) : signExtend(unpack(unbias(opC)));

      Bit#(mbits) sfdB = { getHiddenBit(opB), opB.sfd };
      Bit#(mbits) sfdC = { getHiddenBit(opC), opC.sfd };

      Bool sgnBC = opB.sign != opC.sign;
      Bool infBC = isInfinity(opB) || isInfinity(opC);
      Bool zeroBC = isZero(opB) || isZero(opC);
      Int#(ebits) expBC = expB + expC;

      if (isSNaN(opA)) begin
	 s.res = tagged Valid nanQuiet(opA);
	 s.exc.invalid_op = True;
      end
      else if (isSNaN(opB)) begin
	 s.res = tagged Valid nanQuiet(opB);
	 s.exc.invalid_op = True;
      end
      else if (isSNaN(opC)) begin
	 s.res = tagged Valid nanQuiet(opC);
	 s.exc.invalid_op = True;
      end
      else if (isQNaN(opA)) begin
	 s.res = tagged Valid opA;
      end
      else if (isQNaN(opB)) begin
	 s.res = tagged Valid opB;
      end
      else if (isQNaN(opC)) begin
	 s.res = tagged Valid opC;
      end
      else if ((isInfinity(opB) && isZero(opC)) || (isZero(opB) && isInfinity(opC)) || (isInfinity(opA) && infBC && (opA.sign != sgnBC))) begin
	 // product of zero and infinity or addition of opposite sign infinity
	 s.res = tagged Valid qnan();
	 s.exc.invalid_op = True;
      end
      else if (isInfinity(opA)) begin
	 s.res = tagged Valid opA;
      end
      else if (infBC) begin
	 s.res = tagged Valid infinity(sgnBC);
      end
      else if (isZero(opA) && zeroBC && (opA.sign == sgnBC)) begin
	 s.res = tagged Valid opA;
      end

      fState_S1.enq(tuple7(s,
			   acc,
			   opA,
			   sgnBC,
			   expBC,
			   sfdB,
			   sfdC));
   endrule

   FIFO#(Tuple5#(CommonState#(e,m),
		 Bool,
		 FloatingPoint#(e,m),
		 Bool,
		 Int#(ebits))) fState_S2 <- mkLFIFO;
   FIFO#(Bit#(mmbits)) fProd_S2 <- mkLFIFO;

   // start multiply
   rule s2_stage;
      match { .s, .acc, .opA, .sgnBC, .expBC, .sfdB, .sfdC } <- toGet(fState_S1).get;

      let sfdBC = primMul(sfdB, sfdC);

      fProd_S2.enq(sfdBC);

      fState_S2.enq(tuple5(s,
			   acc,
			   opA,
			   sgnBC,
			   expBC));
   endrule

   FIFO#(Tuple5#(CommonState#(e,m),
		 Bool,
		 FloatingPoint#(e,m),
		 Bool,
		 Int#(ebits))) fState_S3 <- mkLFIFO;
   FIFO#(Bit#(mmbits)) fProd_S3 <- mkLFIFO;

   // passthrough stage for multiply register retiming
   rule s3_stage;
      match { .s, .acc, .opA, .sgnBC, .expBC } <- toGet(fState_S2).get;
      let sfdBC <- toGet(fProd_S2).get;

      fProd_S3.enq(sfdBC);

      fState_S3.enq(tuple5(s,
			   acc,
			   opA,
			   sgnBC,
			   expBC));
   endrule

   FIFO#(Tuple5#(CommonState#(e,m),
		 Bool,
		 FloatingPoint#(e,m),
		 FloatingPoint#(e,m),
		 Bit#(2))) fState_S4 <- mkLFIFO;

   // normalize multiplication result
   rule s4_stage;
      match { .s, .acc, .opA, .sgnBC, .expBC } <- toGet(fState_S3).get;
      let sfdBC <- toGet(fProd_S3).get;

      FloatingPoint#(e,m) bc = defaultValue;
      Bit#(2) guardBC = ?;

      if (s.res matches tagged Invalid) begin
	 if (expBC > fromInteger(maxexp(bc))) begin
	    bc.sign = sgnBC;
	    bc.exp = maxBound - 1;
	    bc.sfd = maxBound;
	    guardBC = '1;

	    s.exc.overflow = True;
	    s.exc.inexact = True;
	 end
	 else if (expBC < (fromInteger(minexp_subnormal(bc))-2)) begin
	    bc.sign = sgnBC;
	    bc.exp = 0;
	    bc.sfd = 0;
	    guardBC = 0;

	    if (|sfdBC == 1) begin
	       guardBC = 1;
	       s.exc.underflow = True;
	       s.exc.inexact = True;
	    end
	 end
	 else begin
	    let shift = fromInteger(minexp(bc)) - expBC;
	    if (shift > 0) begin
	       // subnormal
	       Bit#(1) sfdlsb = |(sfdBC << (fromInteger(valueOf(mmbits)) - shift));

	       sfdBC = sfdBC >> shift;
	       sfdBC[0] = sfdBC[0] | sfdlsb;

	       bc.exp = 0;
	    end
	    else begin
	       bc.exp = cExtend(expBC + fromInteger(bias(bc)));
	    end

	    bc.sign = sgnBC;
	    let y = normalize(bc, sfdBC);
	    bc = tpl_1(y);
	    guardBC = tpl_2(y);
	    s.exc = s.exc | tpl_3(y);
	 end
      end

      fState_S4.enq(tuple5(s,
			   acc,
			   opA,
			   bc,
			   guardBC));
   endrule

   FIFO#(Tuple8#(CommonState#(e,m),
		 Bool,
		 Bool,
		 Bool,
		 Int#(ebits),
		 Int#(ebits),
		 Bit#(m5bits),
		 Bit#(m5bits))) fState_S5 <- mkLFIFO;

   // calculate shift and sign for add
   rule s5_stage;
      match { .s, .acc, .opA, .opBC, .guardBC } <- toGet(fState_S4).get;

      Int#(ebits) expA = isSubNormal(opA) ? fromInteger(minexp(opA)) : signExtend(unpack(unbias(opA)));
      Int#(ebits) expBC = isSubNormal(opBC) ? fromInteger(minexp(opBC)) : signExtend(unpack(unbias(opBC)));

      Bit#(m5bits) sfdA = {1'b0, getHiddenBit(opA), opA.sfd, 3'b0};
      Bit#(m5bits) sfdBC = {1'b0, getHiddenBit(opBC), opBC.sfd, guardBC, 1'b0};

      Bool sub = opA.sign != opBC.sign;

      Int#(ebits) exp = ?;
      Int#(ebits) shift = ?;
      Bit#(m5bits) x = ?;
      Bit#(m5bits) y = ?;
      Bool sgn = ?;

      if ((!acc) || (expBC > expA) || ((expBC == expA) && (sfdBC > sfdA))) begin
	 exp = expBC;
	 shift = expBC - expA;
	 x = sfdBC;
	 y = sfdA;
	 sgn = opBC.sign;
      end
      else begin
	 exp = expA;
	 shift = expA - expBC;
	 x = sfdA;
	 y = sfdBC;
	 sgn = opA.sign;
      end

      fState_S5.enq(tuple8(s,
			   acc,
			   sub,
			   sgn,
			   exp,
			   shift,
			   x,
			   y));
   endrule

   FIFO#(Tuple7#(CommonState#(e,m),
		 Bool,
		 Bool,
		 Bool,
		 Int#(ebits),
		 Bit#(m5bits),
		 Bit#(m5bits))) fState_S6 <- mkLFIFO;

   // shift second add operand
   rule s6_stage;
      match { .s, .acc, .sub, .sgn, .exp, .shift, .x, .y } <- toGet(fState_S5).get;

      if (s.res matches tagged Invalid) begin
	 if (shift < fromInteger(valueOf(m5bits))) begin
	    Bit#(m5bits) guard;

	    guard = y << (fromInteger(valueOf(m5bits)) - shift);
	    y = y >> shift;
	    y[0] = y[0] | (|guard);
	 end
	 else if (|y == 1) begin
	    y = 1;
	 end
      end

      fState_S6.enq(tuple7(s,
			   acc,
			   sub,
			   sgn,
			   exp,
			   x,
			   y));
   endrule

   FIFO#(Tuple7#(CommonState#(e,m),
		 Bool,
		 Bool,
		 Bool,
		 Int#(ebits),
		 Bit#(m5bits),
		 Bit#(m5bits))) fState_S7 <- mkLFIFO;

   // add/subtract sfd
   rule s7_stage;
      match { .s, .acc, .sub, .sgn, .exp, .x, .y } <- toGet(fState_S6).get;

      let sum = x + y;
      let diff = x - y;

      fState_S7.enq(tuple7(s,
			   acc,
			   sub,
			   sgn,
			   exp,
			   sum,
			   diff));
   endrule

   FIFO#(Tuple5#(CommonState#(e,m),
		 Bool,
		 FloatingPoint#(e,m),
		 Bit#(2),
		 Bool)) fState_S8 <- mkLFIFO;

   // normalize addition result
   rule s8_stage;
      match { .s, .acc, .sub, .sgn, .exp, .sum, .diff } <- toGet(fState_S7).get;

      FloatingPoint#(e,m) out = defaultValue;
      Bit#(2) guard = 0;

      if (s.res matches tagged Invalid) begin
	 Bit#(m5bits) sfd;

	 sfd = sub ? diff : sum;

	 out.sign = sgn;
	 out.exp = cExtend(exp + fromInteger(bias(out)));

	 let y = normalize(out, sfd);
	 out = tpl_1(y);
	 guard = tpl_2(y);
	 s.exc = s.exc | tpl_3(y);
      end

      fState_S8.enq(tuple5(s,
			   acc,
			   out,
			   guard,
			   sub));
   endrule

   FIFO#(Tuple2#(FloatingPoint#(e,m),Exception)) fResult_S9 <- mkLFIFO;

   // round result
   rule s9_stage;
      match { .s, .acc, .out, .guard, .sub } <- toGet(fState_S8).get;

      if (s.res matches tagged Valid .x) begin
	 out = x;
      end
      else begin
	 let y = round(s.rmode, out, guard);
	 out = tpl_1(y);
	 s.exc = s.exc | tpl_2(y);

	 // adjust sign for exact zero result
	 if (acc && isZero(out) && !s.exc.inexact && sub) begin
	    out.sign = (s.rmode == Rnd_Minus_Inf);
	 end
      end

      fResult_S9.enq(tuple2(out,s.exc));
   endrule

   interface request = toPut(fOperand_S0);
   interface response = toGet(fResult_S9);

endmodule : mkFloatingPointFusedMultiplyAccumulate

////////////////////////////////////////////////////////////////////////////////
/// FixedFloatCVT instance
////////////////////////////////////////////////////////////////////////////////

typeclass FixedFloatCVT#(type tfl, type tfx);
   function Tuple2#(tfl,Exception) vFixedToFloat(tfx fx, UInt#(ln) frac, RoundMode rmode);
   function Tuple2#(tfx,Exception) vFloatToFixed(UInt#(ln) frac, tfl fl, RoundMode rmode);
endtypeclass

instance FixedFloatCVT#(FloatingPoint#(e,m),UInt#(n))
   provisos(
      // per request of bsc
      Add#(1, a__, TMax#(n, TAdd#(m, 2))),
      Add#(m, b__, TMax#(n, TAdd#(3, m))),
      Add#(1, c__, TMax#(n, TAdd#(3, m)))
      );
   function Tuple2#(FloatingPoint#(e,m),Exception) vFixedToFloat(UInt#(n) fx, UInt#(ln) frac, RoundMode rmode);
      FloatingPoint#(e,m) out = defaultValue;
      Exception exc = defaultValue;

      Bit#(TMax#(n,TAdd#(3,m))) sfd = zExtendLSB(pack(fx));
      let shft = countZerosMSB(sfd);
      Int#(TMax#(ln,TMax#(TLog#(TAdd#(1,TMax#(n,TAdd#(3,m)))),TAdd#(1,e)))) exp = fromInteger(valueOf(n)) - zeroExtend(unpack(pack(frac))) - zeroExtend(unpack(pack(shft))) - 1;

      if (fx == 0) begin
	 out = zero(False);
      end
      else if (shft == fromInteger(valueOf(n))) begin
	 out = zero(False);
      end
      else if (exp > fromInteger(maxexp(out))) begin
	 out = infinity(False);
	 exc.overflow = True;
      end
      else if (exp < fromInteger(minexp_subnormal(out))) begin
	 out = zero(False);
	 exc.underflow = True;
      end
      else if (exp < fromInteger(minexp(out))) begin
	 Bit#(2) guard = 0;

	 out.sign = False;
	 out.exp = 0;

	 sfd = sfd << shft;

	 out.sfd = pack(truncateLSB(sfd));
	 sfd = sfd << fromInteger(valueOf(m));

	 guard[1] = truncateLSB(sfd);
	 sfd = sfd << 1;
	 guard[0] = |sfd;

	 let x = round(rmode, out, guard);
	 out = tpl_1(x);
	 exc = tpl_2(x);
      end
      else begin
	 Bit#(2) guard = 0;

	 out.sign = False;

	 Int#(TAdd#(1,e)) x = truncate(exp + fromInteger(bias(out)));
	 out.exp = truncate(pack(x));

	 sfd = sfd << shft;

	 // hidden bit
	 sfd = sfd << 1;

	 out.sfd = pack(truncateLSB(sfd));
	 sfd = sfd << fromInteger(valueOf(m));

	 guard[1] = truncateLSB(sfd);
	 sfd = sfd << 1;
	 guard[0] = |sfd;

	 let y = round(rmode, out, guard);
	 out = tpl_1(y);
	 exc = tpl_2(y);
      end

      return tuple2(out,exc);
   endfunction

   function Tuple2#(UInt#(n),Exception) vFloatToFixed(UInt#(ln) frac, FloatingPoint#(e,m) fl, RoundMode rmode);
      UInt#(n) out = 0;
      Exception exc = defaultValue;

      if (isNaN(fl)) begin
	 out = minBound;
	 exc.invalid_op = True;
      end
      else if (isInfinity(fl)) begin
	 out = maxBound;
	 exc.invalid_op = True;
      end
      else if (fl.sign) begin
	 out = minBound;
	 exc.invalid_op = True;
      end
      else if (isZero(fl)) begin
	 out = 0;
      end
      else begin
	 // todo: does this work for subnormal?

	 UInt#(TAdd#(n,TAdd#(m,2))) sfd = unpack(zExtendLSB({getHiddenBit(fl), fl.sfd}));
	 Int#(TAdd#(TAdd#(TAdd#(e,1),TLog#(m)),ln)) shft = -signExtend(unpack(unbias(fl))) + fromInteger(valueOf(n)) - 1 - zeroExtend(unpack(pack(frac)));

	 if (shft < 0) begin
	    out = maxBound;
	    exc.invalid_op = True;  // overflow signals invalid op
	 end
	 else if (shft > fromInteger(valueOf(n))) begin
	    out = 0;
	    exc.inexact = True;
	 end
	 else begin
	    Bit#(2) guard = 0;

	    sfd = sfd >> shft;

	    out = unpack(truncateLSB(pack(sfd)));
	    sfd = sfd << fromInteger(valueOf(n));

	    guard[1] = truncateLSB(pack(sfd));
	    sfd = sfd << 1;
	    guard[0] = |pack(sfd);

	    if (|guard == 1) begin
	       exc.inexact = True;
	    end

	    Bool inc = False;

	    case (rmode)
	       Rnd_Nearest_Even:
	       case (guard)
		  'b10: inc = (lsb(out) == 'b1);
		  'b11: inc = True;
	       endcase
	       Rnd_Plus_Inf: inc = (guard != 0);
	       Rnd_Minus_Inf: inc = False;
	       Rnd_Zero: inc = False;
	    endcase

	    if (inc) begin
	       if (out == maxBound) begin
		  exc.invalid_op = True;  // overflow signals invalid op
	       end
	       else begin
		  out = out + 1;
	       end
	    end
	 end
      end

      return tuple2(out,exc);
   endfunction
endinstance

instance FixedFloatCVT#(FloatingPoint#(e,m),Int#(n))
   provisos(
      // per request of bsc
      Add#(1, a__, n),
      Add#(1, b__, TMax#(n, TAdd#(3, m))),
      Add#(m, c__, TMax#(n, TAdd#(3, m)))
      );
   function Tuple2#(FloatingPoint#(e,m),Exception) vFixedToFloat(Int#(n) fx, UInt#(ln) frac, RoundMode rmode);
      FloatingPoint#(e,m) out = defaultValue;
      Exception exc = defaultValue;

      Bool sign = unpack(msb(pack(fx)));
      Bit#(TMax#(n,TAdd#(3,m))) sfd = zExtendLSB(pack(sign ? -fx : fx));
      let shft = countZerosMSB(sfd);
      Int#(TMax#(ln,TMax#(TLog#(TAdd#(1,TMax#(n,TAdd#(3,m)))),TAdd#(1,e)))) exp = fromInteger(valueOf(n)) - zeroExtend(unpack(pack(frac))) - zeroExtend(unpack(pack(shft))) - 1;

      if (fx == 0) begin
	 out = zero(False);
      end
      else if (shft == fromInteger(valueOf(n))) begin
	 out = zero(sign);
      end
      else if (exp > fromInteger(maxexp(out))) begin
	 out = infinity(sign);
	 exc.overflow = True;
      end
      else if (exp < fromInteger(minexp_subnormal(out))) begin
	 out = zero(sign);
	 exc.underflow = True;
      end
      else if (exp < fromInteger(minexp(out))) begin
	 Bit#(2) guard = 0;

	 out.sign = sign;
	 out.exp = 0;

	 sfd = sfd << shft;

	 out.sfd = pack(truncateLSB(sfd));
	 sfd = sfd << fromInteger(valueOf(m));

	 guard[1] = truncateLSB(sfd);
	 sfd = sfd << 1;
	 guard[0] = |sfd;

	 let x = round(rmode, out, guard);
	 out = tpl_1(x);
	 exc = tpl_2(x);
      end
      else begin
	 Bit#(2) guard = 0;

	 out.sign = sign;

	 Int#(TAdd#(1,e)) x = truncate(exp + fromInteger(bias(out)));
	 out.exp = truncate(pack(x));

	 sfd = sfd << shft;

	 // hidden bit
	 sfd = sfd << 1;

	 out.sfd = pack(truncateLSB(sfd));
	 sfd = sfd << fromInteger(valueOf(m));

	 guard[1] = truncateLSB(sfd);
	 sfd = sfd << 1;
	 guard[0] = |sfd;

	 let y = round(rmode, out, guard);
	 out = tpl_1(y);
	 exc = tpl_2(y);
      end

      return tuple2(out,exc);
   endfunction

   function Tuple2#(Int#(n),Exception) vFloatToFixed(UInt#(ln) frac, FloatingPoint#(e,m) fl, RoundMode rmode);
      Int#(n) out = 0;
      Exception exc = defaultValue;

      if (isNaN(fl)) begin
	 out = minBound;
	 exc.invalid_op = True;
      end
      else if (isInfinity(fl)) begin
	 out = fl.sign ? minBound : maxBound;
	 exc.invalid_op = True;
      end
      else if (isZero(fl)) begin
	 out = 0;
      end
      else begin
	 // todo: does this work for subnormal?

	 // needs to be large so bits aren't lost before rounding
	 Int#(TAdd#(n,TAdd#(m,2))) sfd = fl.sign ? -unpack(zExtendLSB({1'b0, getHiddenBit(fl), fl.sfd})) : unpack(zExtendLSB({1'b0, getHiddenBit(fl), fl.sfd}));
	 Int#(TAdd#(TAdd#(TAdd#(e,1),TLog#(m)),ln)) shft = -signExtend(unpack(unbias(fl))) + fromInteger(valueOf(n)) - 2 - zeroExtend(unpack(pack(frac)));

	 if (shft == -1) begin
	    Bit#(TAdd#(n,1)) out1;
	    Bit#(2) guard;

	    out1 = truncateLSB(pack(sfd));
	    sfd = sfd << fromInteger(valueOf(n) + 1);

	    guard[1] = truncateLSB(pack(sfd));
	    sfd = sfd << 1;
	    guard[0] = |pack(sfd);

	    Bool inc = False;

	    case (rmode)
	       Rnd_Nearest_Even:
	       case (guard)
		  'b10: inc = (lsb(out1) == 'b1);
		  'b11: inc = True;
	       endcase
	       Rnd_Plus_Inf: inc = (guard != 0);
	       Rnd_Minus_Inf: inc = False;
	       Rnd_Zero: inc = (msb(out1) == 'b1) ? (guard != 0) : False;
	    endcase

	    if (inc) begin
	       out1 = out1 + 1;
	    end

	    if (truncateLSB(pack(out1)) == 2'b11) begin
	       out = unpack(truncate(out1));

	       if (|guard == 1) begin
		  exc.inexact = True;
	       end
	    end
	    else begin
	       out = fl.sign ? minBound : maxBound;
	       exc.invalid_op = True;  // overflow signals invalid op
	    end
	 end
	 else if (shft < 0) begin
	    out = fl.sign ? minBound : maxBound;
	    exc.invalid_op = True;  // overflow signals invalid op
	 end
	 else if (shft > fromInteger(valueOf(n))) begin
	    out = 0;
	    exc.inexact = True;
	 end
	 else begin
	    Bit#(2) guard = 0;

	    sfd = sfd >> shft;

	    out = unpack(truncateLSB(pack(sfd)));
	    sfd = sfd << fromInteger(valueOf(n));

	    guard[1] = truncateLSB(pack(sfd));
	    sfd = sfd << 1;
	    guard[0] = |pack(sfd);

	    if (|guard == 1) begin
	       exc.inexact = True;
	    end

	    Bool inc = False;

	    case (rmode)
	       Rnd_Nearest_Even:
	       case (guard)
		  'b10: inc = (lsb(out) == 'b1);
		  'b11: inc = True;
	       endcase
	       Rnd_Plus_Inf: inc = (guard != 0);
	       Rnd_Minus_Inf: inc = False;
	       Rnd_Zero: inc = (msb(out) == 'b1) ? (guard != 0) : False;
	    endcase

	    if (inc) begin
	       if (out == maxBound) begin
		  exc.invalid_op = True;  // overflow signals invalid op
	       end
	       else begin
		  out = out + 1;
	       end
	    end

	 end
      end

      return tuple2(out,exc);
   endfunction
endinstance

// Note: this is not well tested
instance FixedFloatCVT#(FloatingPoint#(e,m), FixedPoint#(isize,fsize))
   provisos(
      Add#(isize, fsize, n),
      // per request of bsc
      Add#(1, a__, n),
      Add#(1, b__, TMax#(n, TAdd#(3, m))),
      Add#(m, c__, TMax#(n, TAdd#(3, m)))
      );
   function Tuple2#(FloatingPoint#(e,m),Exception) vFixedToFloat(FixedPoint#(isize,fsize) fx, UInt#(ln) frac, RoundMode rmode);
      FloatingPoint#(e,m) out = defaultValue;
      Exception exc = defaultValue;

      Bit#(TMax#(n,TAdd#(3,m))) sfd = zExtendLSB({fx.i,fx.f});
      let shft = countZerosMSB(sfd);
      Int#(TMax#(ln,TMax#(TLog#(TAdd#(1,TMax#(n,TAdd#(3,m)))),TAdd#(1,e)))) exp = fromInteger(valueOf(n)) - zeroExtend(unpack(pack(frac))) - zeroExtend(unpack(pack(shft))) - 1;

      if (sfd == 0) begin
	 out = zero(False);
      end
      else if (shft == fromInteger(valueOf(n))) begin
	 out = zero(False);
      end
      else if (exp > fromInteger(maxexp(out))) begin
	 out = infinity(False);
	 exc.overflow = True;
      end
      else if (exp < fromInteger(minexp_subnormal(out))) begin
	 out = zero(False);
	 exc.underflow = True;
      end
      else if (exp < fromInteger(minexp(out))) begin
	 Bit#(2) guard = 0;

	 out.sign = False;
	 out.exp = 0;

	 sfd = sfd << shft;

	 out.sfd = pack(truncateLSB(sfd));
	 sfd = sfd << fromInteger(valueOf(m));

	 guard[1] = truncateLSB(sfd);
	 sfd = sfd << 1;
	 guard[0] = |sfd;

	 let x = round(rmode, out, guard);
	 out = tpl_1(x);
	 exc = tpl_2(x);
      end
      else begin
	 Bit#(2) guard = 0;

	 out.sign = False;

	 Int#(TAdd#(1,e)) x = truncate(exp + fromInteger(bias(out)));
	 out.exp = truncate(pack(x));

	 sfd = sfd << shft;

	 // hidden bit
	 sfd = sfd << 1;

	 out.sfd = pack(truncateLSB(sfd));
	 sfd = sfd << fromInteger(valueOf(m));

	 guard[1] = truncateLSB(sfd);
	 sfd = sfd << 1;
	 guard[0] = |sfd;

	 let y = round(rmode, out, guard);
	 out = tpl_1(y);
	 exc = tpl_2(y);
      end

      return tuple2(out,exc);
   endfunction

   function Tuple2#(FixedPoint#(isize,fsize),Exception) vFloatToFixed(UInt#(ln) frac, FloatingPoint#(e,m) fl, RoundMode rmode);
      Int#(n) out = 0;
      Exception exc = defaultValue;

      if (isNaN(fl)) begin
	 out = minBound;
	 exc.invalid_op = True;
      end
      else if (isInfinity(fl)) begin
	 out = fl.sign ? minBound : maxBound;
	 exc.invalid_op = True;
      end
      else if (isZero(fl)) begin
	 out = 0;
      end
      else begin
	 // todo: does this work for subnormal?

	 // needs to be large so bits aren't lost before rounding
	 Int#(TAdd#(n,TAdd#(m,2))) sfd = fl.sign ? -unpack(zExtendLSB({1'b0, getHiddenBit(fl), fl.sfd})) : unpack(zExtendLSB({1'b0, getHiddenBit(fl), fl.sfd}));
	 Int#(TAdd#(TAdd#(TAdd#(e,1),TLog#(m)),ln)) shft = -signExtend(unpack(unbias(fl))) + fromInteger(valueOf(n)) - 2 - zeroExtend(unpack(pack(frac)));

	 if (shft == -1) begin
	    Bit#(TAdd#(n,1)) out1;
	    Bit#(2) guard;

	    out1 = truncateLSB(pack(sfd));
	    sfd = sfd << fromInteger(valueOf(n) + 1);

	    guard[1] = truncateLSB(pack(sfd));
	    sfd = sfd << 1;
	    guard[0] = |pack(sfd);

	    Bool inc = False;

	    case (rmode)
	       Rnd_Nearest_Even:
	       case (guard)
		  'b10: inc = (lsb(out1) == 'b1);
		  'b11: inc = True;
	       endcase
	       Rnd_Plus_Inf: inc = (guard != 0);
	       Rnd_Minus_Inf: inc = False;
	       Rnd_Zero: inc = (msb(out1) == 'b1) ? (guard != 0) : False;
	    endcase

	    if (inc) begin
	       out1 = out1 + 1;
	    end

	    if (truncateLSB(pack(out1)) == 2'b11) begin
	       out = unpack(truncate(out1));

	       if (|guard == 1) begin
		  exc.inexact = True;
	       end
	    end
	    else begin
	       out = fl.sign ? minBound : maxBound;
	       exc.invalid_op = True;  // overflow signals invalid op
	    end
	 end
	 else if (shft < 0) begin
	    out = fl.sign ? minBound : maxBound;
	    exc.invalid_op = True;  // overflow signals invalid op
	 end
	 else if (shft > fromInteger(valueOf(n))) begin
	    out = 0;
	    exc.inexact = True;
	 end
	 else begin
	    Bit#(2) guard = 0;

	    sfd = sfd >> shft;

	    out = unpack(truncateLSB(pack(sfd)));
	    sfd = sfd << fromInteger(valueOf(n));

	    guard[1] = truncateLSB(pack(sfd));
	    sfd = sfd << 1;
	    guard[0] = |pack(sfd);

	    if (|guard == 1) begin
	       exc.inexact = True;
	    end

	    Bool inc = False;

	    case (rmode)
	       Rnd_Nearest_Even:
	       case (guard)
		  'b10: inc = (lsb(out) == 'b1);
		  'b11: inc = True;
	       endcase
	       Rnd_Plus_Inf: inc = (guard != 0);
	       Rnd_Minus_Inf: inc = False;
	       Rnd_Zero: inc = (msb(out) == 'b1) ? (guard != 0) : False;
	    endcase

	    if (inc) begin
	       if (out == maxBound) begin
		  exc.invalid_op = True;  // overflow signals invalid op
	       end
	       else begin
		  out = out + 1;
	       end
	    end

	 end
      end

      FixedPoint#(isize,fsize) fx;
      fx.i = truncateLSB(pack(out));
      fx.f = truncate(pack(out));

      return tuple2(fx,exc);
   endfunction
endinstance


endpackage: FloatingPoint
