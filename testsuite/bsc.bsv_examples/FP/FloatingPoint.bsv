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
import DefaultValue      ::*;
import FShow             ::*;
import GetPut            ::*;
import ClientServer      ::*;
import FIFO              ::*;
import FIFOF             ::*;
import SpecialFIFOs      ::*;
import DReg              ::*;

////////////////////////////////////////////////////////////////////////////////
/// Types
////////////////////////////////////////////////////////////////////////////////
typedef struct {
   Bool        sign;
   Bit#(e)     exp;
   Bit#(m)     sfd;
   Bit#(2)     round;
   Bit#(1)     sticky;
} FloatingPoint#(numeric type e, numeric type m) deriving (Bits);

instance DefaultValue#( FloatingPoint#(e,m) );
   defaultValue = FloatingPoint {
      sign:       False,
      exp:        0,
      sfd:        0,
      round:      0,
      sticky:     0
      };
endinstance

instance Eq#( FloatingPoint#(e,m) );
   function Bool \== ( FloatingPoint#(e,m) a, FloatingPoint#(e,m) b );
      Bool is_equal  = (a.sign == b.sign) && (a.exp == b.exp) && (a.sfd == b.sfd);
      Bool a_is_zero = (a.exp == 0) && (a.sfd == 0);
      Bool b_is_zero = (b.exp == 0) && (b.sfd == 0);
      return (is_equal || (a_is_zero && b_is_zero));
   endfunction
   function Bool \/= ( FloatingPoint#(e,m) a, FloatingPoint#(e,m) b );
      Bool is_equal  = (a.sign == b.sign) && (a.exp == b.exp) && (a.sfd == b.sfd);
      Bool a_is_zero = (a.exp == 0) && (a.sfd == 0);
      Bool b_is_zero = (b.exp == 0) && (b.sfd == 0);
      return !(is_equal || (a_is_zero && b_is_zero));
   endfunction
endinstance

instance FShow#( FloatingPoint#(e,m) );
   function Fmt fshow( FloatingPoint#(e,m) value );
      Int#(e) realexp  = unpack(value.exp) - fromInteger(bias(value));
      case (value.exp) 
      	 0: return $format("<Float (-1)^%d * 0.%b * 2^%d - %b %b>", pack(value.sign), value.sfd, minexp(value)-1, value.round, value.sticky);
      	 unpack('1): begin
      			if (value.sfd == 0) return $format("<Float (-1)^%d * infinity>", pack(value.sign));
      			else if (msb(value.sfd) == 1) return $format("<Float QNaN>");
      			else return $format("<Float SNaN>");
      		     end
      	 default: return $format("<Float (-1)^%d * 1.%b * 2^%d - %b %b>", pack(value.sign), value.sfd, realexp, value.round, value.sticky);
      endcase
   endfunction
endinstance

typedef enum {
     Rnd_Nearest_Even
   , Rnd_Nearest_Away_Zero
   , Rnd_Plus_Inf 
   , Rnd_Minus_Inf
   , Rnd_Zero
} RoundMode deriving (Bits, Eq);

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

typedef enum {
     Msg_Exact
   , Msg_Invalid_Op
   , Msg_Divide_0
   , Msg_Overflow
   , Msg_Underflow
   , Msg_Inexact
} Message deriving (Bits, Eq);

instance FShow#( Message );
   function Fmt fshow( Message value );
      case(value)
	 Msg_Exact:      return $format("<Message: Exact>");
	 Msg_Invalid_Op: return $format("<Message: Invalid Op>");
	 Msg_Divide_0:   return $format("<Message: Divide By 0>");
	 Msg_Overflow:   return $format("<Message: Overflow>");
	 Msg_Underflow:  return $format("<Message: Underflow>");
	 Msg_Inexact:    return $format("<Message: Inexact>");
      endcase
   endfunction
endinstance

////////////////////////////////////////////////////////////////////////////////
/// Float Formats
////////////////////////////////////////////////////////////////////////////////
typedef struct {
   Bool        sign;
   Bit#(5)     exp;
   Bit#(10)    sfd;
} Float16 deriving (Bits, Eq);

typedef struct {
   Bool        sign;
   Bit#(8)     exp;
   Bit#(23)    sfd;
} Float32 deriving (Bits, Eq);

typedef struct {
   Bool        sign;
   Bit#(11)    exp;
   Bit#(52)    sfd;
} Float64 deriving (Bits, Eq);		

typedef struct {
   Bool        sign;
   Bit#(15)    exp;
   Bit#(112)   sfd;
} Float128 deriving (Bits, Eq);		

typedef FloatingPoint#(5,10)   FP16; // Half
typedef Float16                Half;
typedef FloatingPoint#(8,23)   FP32; // Float
typedef Float32                Float;
typedef FloatingPoint#(11,52)  FP64; // Double
typedef Float64                Double;
typedef FloatingPoint#(15,112) FP128; // Quad
typedef Float128               Quad;

typeclass FloatingPointTC#(type a, numeric type e, numeric type m)
   dependencies(a determines (e,m));
   function FloatingPoint#(e,m) toFP(a value);
   function a                   fromFP(FloatingPoint#(e,m) value);
endtypeclass

instance FloatingPointTC#(FloatingPoint#(e,m), e, m);
   function toFP   = id;
   function fromFP = id;
endinstance

instance FloatingPointTC#(Half, 5, 10);
   function FloatingPoint#(5,10) toFP(Half value);
      FloatingPoint#(5,10) y = unpack(0);
      y.sign = value.sign;
      y.exp  = value.exp;
      y.sfd  = value.sfd;
      return y;
   endfunction
   function Half fromFP(FloatingPoint#(5,10) value);
      Half y = unpack(0);
      y.sign = value.sign;
      y.exp  = value.exp;
      y.sfd  = value.sfd;
      return y;
   endfunction
endinstance

// TODO: Add a general instance for Half conversion with e/m instead of 5/10

instance FloatingPointTC#(Float, 8, 23);
   function FloatingPoint#(8,23) toFP(Float value);
      FloatingPoint#(8,23) y = unpack(0);
      y.sign = value.sign;
      y.exp  = value.exp;
      y.sfd  = value.sfd;
      return y;
   endfunction
   function Float fromFP(FloatingPoint#(8,23) value);
      Float y = unpack(0);
      y.sign = value.sign;
      y.exp  = value.exp;
      y.sfd  = value.sfd;
      return y;
   endfunction
endinstance

// TODO: Add a general instance for Float conversion with e/m instead of 8/23

instance FloatingPointTC#(Double, 11, 52);
   function FloatingPoint#(11,52) toFP(Double value);
      FloatingPoint#(11,52) y = unpack(0);
      y.sign = value.sign;
      y.exp  = value.exp;
      y.sfd  = value.sfd;
      return y;
   endfunction
   function Double fromFP(FloatingPoint#(11,52) value);
      Double y = unpack(0);
      y.sign = value.sign;
      y.exp  = value.exp;
      y.sfd  = value.sfd;
      return y;
   endfunction
endinstance

// TODO: Add a general instance for Double conversion with e/m instead of 11/52

instance FloatingPointTC#(Quad, 15, 112);
   function FloatingPoint#(15,112) toFP(Quad value);
      FloatingPoint#(15,112) y = unpack(0);
      y.sign = value.sign;
      y.exp  = value.exp;
      y.sfd  = value.sfd;
      return y;
   endfunction
   function Quad fromFP(FloatingPoint#(15,112) value);
      Quad y = unpack(0);
      y.sign = value.sign;
      y.exp  = value.exp;
      y.sfd  = value.sfd;
      return y;
   endfunction
endinstance

// TODO: Add a general instance for Quad conversion with e/m instead of 15/112



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
      sfd:      0,
      round:    0,
      sticky:   0
      };
endfunction

function Bool isInfinity( FloatingPoint#(e,m) din );
   return ((&din.exp == 1) && (din.sfd == 0));
endfunction

function FloatingPoint#(e,m) qnan();
   return FloatingPoint {
      sign:     False,
      exp:      maxBound,
      sfd:      maxBound,
      round:    0,
      sticky:   0
      };
endfunction

function Bool isQNaN( FloatingPoint#(e,m) din );
   return ((&din.exp == 1) && (&din.sfd == 1));
endfunction

function FloatingPoint#(e,m) snan();
   return FloatingPoint {
      sign:     False,
      exp:      unpack('1),
      sfd:      1,
      round:    0,
      sticky:   0
      };
endfunction

function Bool isSNaN( FloatingPoint#(e,m) din );
   return ((&din.exp == 1) && (|din.sfd == 1) && (&din.sfd == 0));
endfunction

function FloatingPoint#(e,m) zero(Bool sign);
   return FloatingPoint {
      sign:     sign,
      exp:      0,
      sfd:      0,
      round:    0,
      sticky:   0
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
   Bit#(x) sfd = cExtendLSB({ getHiddenBit(din), din.sfd, din.round, din.sticky });
   Bit#(1) hidden; Bit#(m) s; Bit#(2) r; Bit#(m) rest;
   { hidden, s, r, rest } = cExtendLSB(sfd >> amt);
   din.sticky = (amt > fromInteger(valueof(m))) ? |din.sfd : |rest;
   din.sfd    = s;
   din.round  = r;
   return din;
endfunction

function FloatingPoint#(e,m) round_default( FloatingPoint#(e,m) din );
   return round(Rnd_Nearest_Even, din);
endfunction

function FloatingPoint#(e,m) round( RoundMode rmode, FloatingPoint#(e,m) din )
   provisos(  Add#(m, 1, m1)
	    , Add#(m, 2, m2)
	    );
   
   FloatingPoint#(e,m) out = defaultValue;
   
   if (isNaNOrInfinity(din)) begin
      out = din;
   end
   else begin
      out.sign = din.sign;
      out.exp  = din.exp;
      
      Bit#(TAdd#(m,1)) sfd0 = zExtend(din.sfd);
      Bit#(TAdd#(m,1)) sfd1 = zExtend(din.sfd) + 1;
      
      Bool may_overflow = (msb(sfd1) == 1) && (din.exp == fromInteger(maxexp(din)));
      Bool needs_normalization = (msb(sfd1) == 1) && (din.exp != fromInteger(maxexp(din)));
      Bool any_round_set = (|din.round == 1) || (din.sticky == 1);
      
      case(rmode)
	 Rnd_Nearest_Even: 
	 begin
	    case({ lsb(din.sfd), din.round, din.sticky }) 
	       4'b0000,
	       4'b0001,
	       4'b0010,
	       4'b0011,
	       4'b0100,
	       4'b1000,
	       4'b1001,
	       4'b1010,
	       4'b1011: out.sfd = cExtend(sfd0);
	       
	       4'b0101, 
	       4'b0110, 
	       4'b0111, 
	       4'b1100, 
	       4'b1101, 
	       4'b1110, 
	       4'b1111: begin
			   if (may_overflow) begin
			      out = infinity(out.sign);
			   end
			   else if (needs_normalization) begin
			      out.exp = out.exp + 1;
			      if (out.exp > fromInteger(maxexp(out))) begin
				 out = infinity(out.sign);
			      end
			      else begin
				 out.sfd = cExtend(sfd1>>1);
			      end
			   end
			   else begin
			      out.sfd = cExtend(sfd1);
			   end
			end
	    endcase
	 end
	 
	 Rnd_Nearest_Away_Zero:
	 begin
	    if (msb(din.round) == 1) begin
	       if (may_overflow) begin
		  out = infinity(out.sign);
	       end
	       else if (needs_normalization) begin
		  out.exp = out.exp + 1;
		  if (out.exp > fromInteger(maxexp(out))) begin
		     out = infinity(out.sign);
		  end
		  else begin
		     out.sfd = cExtend(sfd1>>1);
		  end
	       end
	       else begin
		  out.sfd = cExtend(sfd1);
	       end
	    end
	    else begin
	       out.sfd = cExtend(sfd0);
	    end
	 end      
	 
	 Rnd_Plus_Inf:
	 begin
	    if (din.sign) begin
	       out.sfd = cExtend(sfd0);
	    end
	    else begin
	       if (may_overflow) begin
		  //msg = Msg_Overflow;
		  out = infinity(out.sign);
	       end
	       else begin
		  if (any_round_set) begin
		     if (needs_normalization) begin
			out.exp = out.exp + 1;
			if (out.exp > fromInteger(maxexp(out))) begin
			   out = infinity(out.sign);
			end
			else begin
			   out.sfd = cExtend(sfd1>>1);
			end
		     end
		     else begin
			out.sfd = cExtend(sfd1);
		     end
		  end
		  else begin
		     out.sfd = cExtend(sfd0);
		  end
	       end
	    end
	 end
	 
	 Rnd_Minus_Inf:
	 begin
	    if (din.sign) begin
	       if (may_overflow) begin
		  //msg = Msg_Overflow;
		  out = infinity(out.sign);
	       end
	       else begin
		  if (any_round_set) begin
		     if (needs_normalization) begin
			out.exp = out.exp + 1;
			if (out.exp > fromInteger(maxexp(out))) begin
			   out = infinity(out.sign);
			end
			else begin
			   out.sfd = cExtend(sfd1>>1);
			end
		     end
		     else begin
			out.sfd = cExtend(sfd1);
		     end
		  end
		  else begin
		     out.sfd = cExtend(sfd0);
		  end
	       end
	    end
	    else begin
	       out.sfd = cExtend(sfd0);
	    end
	 end
	 
	 Rnd_Zero:
	 begin
	    out.sfd = cExtend(sfd0);
	 end
      endcase
   end
      
   return out;
endfunction

function FloatingPoint#(e,m) normalize( FloatingPoint#(e,m) din, Bit#(x) sfdin )
   provisos(  Add#(m, a, x)
	    , Add#(4, p, a)
	    , Bits#(Tuple5#(Bit#(1),Bit#(1),Bit#(m),Bit#(2),Bit#(p)), x)
	    , Bits#(Tuple4#(Bit#(1),Bit#(m),Bit#(2),Bit#(TAdd#(p,1))), x)
	    );
   
   FloatingPoint#(e,m) out = din;
   
   Bit#(1) rcarry; Bit#(1) rhidden; Bit#(m) rsfd; Bit#(2) rround; Bit#(p) rsticky;
   { rcarry, rhidden, rsfd, rround, rsticky } = unpack(sfdin);
   
   // We have a carry out, so shift it to the hidden bit and adjust the exponent to compensate.
   if (rcarry == 1) begin
      Bit#(1) chidden; Bit#(m) csfd; Bit#(2) cround; Bit#(TAdd#(p,1)) csticky;
      { chidden, csfd, cround, csticky } = unpack(sfdin);
      out.exp = out.exp + 1;
      if (out.exp > fromInteger(2*bias(out))) begin
	 out = infinity(out.sign); // overflow
      end
      else begin
	 out.sfd    = csfd;
	 out.round  = cround;
	 out.sticky = |csticky;
      end
   end
   // We have a denormalized result
   else if (out.exp == 0) begin
      // in the case where the operation overflows from subnormal to normal,
      // normalize the result by making it normal!
      if (rhidden == 1) begin
	 out.exp    = 1; // out.exp + 1;
	 out.sfd    = rsfd;
	 out.round  = rround;
	 out.sticky = |rsticky;
      end
      else begin
	 out.sfd    = rsfd;
	 out.round  = rround;
	 out.sticky = |rsticky;
      end
   end
   // Already normalized!
   else if (rhidden == 1) begin
      out.sfd    = rsfd;
      out.round  = rround;
      out.sticky = |rsticky;
   end
   else begin
      let msbindex = findIndexOneMSB_(rsfd);
      if (msbindex == 0) begin
	 out.exp    = 0;
	 out.sfd    = 0;
	 out.round  = 0;
	 out.sticky = 0;
      end
      else begin
	 Integer shift = valueof(m) - msbindex + 1;
	 Int#(TAdd#(e,1)) exp = signExtend(unpack(unbias(out)));
	 if ((exp - fromInteger(shift)) < fromInteger(minexp_subnormal(out))) begin
	    out = zero(out.sign); // underflow
	 end
	 else if ((exp - fromInteger(shift)) < fromInteger(minexp(out))) begin
	    out.exp    = 0;
	    out.sfd    = cExtendLSB({ rsfd, rround } << (exp+fromInteger(bias(out))));
	    out.round  = rround << (exp+fromInteger(bias(out)));
	    out.sticky = |rsticky;
	 end
	 else begin
	    out.exp    = out.exp - fromInteger(shift);
	    out.sfd    = cExtendLSB({ rsfd, rround } << shift);
	    out.round  = rround << shift;
	    out.sticky = |rsticky;
	 end
      end
   end
   
   return out;
endfunction

function Int#(32) toInt32(FloatingPoint#(e,m) din);
   Int#(32) res = 0;
   
   if (isNaN(din))
      res = 0;
   else if (isInfinity(din))
      res = (din.sign) ? unpack('h80000000) : unpack('h7FFFFFFF);
   else begin
      // if the quantity is less than +/-1, it is zero.
      if (din.exp >= fromInteger(bias(din))) begin
	 // be sure to re-add the hidden bit when converting.
	 Bit#(TAdd#(m,1)) y = { 1, din.sfd };
	 y = y >> (fromInteger(bias(din)) + fromInteger(valueOf(m)) - din.exp);
	 Bit#(32) r = cExtend(y);
	 
	 if (din.sign) res = unpack(~r + 1);
	 else          res = unpack(r);
      end
   end
   return res;
endfunction

function FloatingPoint#(e,m) fromInt32(Int#(32) x)
   provisos( Add#(_, 1, m) );
   
   FloatingPoint#(e,m) res = defaultValue;
   Bool issue = False;
   
   Bit#(e) exp = 0;
   
   // the msb of the int is the sign bit.
   res.sign = msb(x) == 1;

   // take the absolute value of the int32
   // which means the 2-complement if it is
   // negative.
   Bit#(32) v = 0;
   if (res.sign) v = ~pack(x)+1;
   else          v = pack(x);
   
   if (x != 0) begin
      exp = cExtend(findIndexOneLSB(v));
      v   = v >> exp;
      Bit#(TAdd#(m,1)) sx = 0;
      
      // if the quantity cannot be represented by the given
      // floating point format, it is infinity!
      if (findIndexOneMSB_(v) > valueof(m)) begin
	 res = infinity(res.sign);
      end
      else begin
	 sx = zExtend(v);
      	 Bit#(m) mval = cExtend(sx);
	 res.exp = exp + fromInteger(bias(res)) + cExtend(findIndexOneMSB(mval)) - 1;//fromInteger(exp + bias(res) + msbindex - 1);
	 res.sfd = mval << (fromInteger(valueof(m)) - (findIndexOneMSB(mval) - 1));
      end
   end
   return res;
endfunction

function FloatingPoint#(e,m) fract(FloatingPoint#(e,m) din);
   FloatingPoint#(e,m) res = din;
   
   // this routine extracts the fractional portion of a floating point number, i.e.
   //  123.456 would return 0.456.
   
   // if the value is not a number, provide not a number result
   if (isNaN(din))
      res = din;
   else if (isInfinity(din)) // if the number is infinity, signal NaN
      res = snan();
   else if (din.exp < fromInteger(bias(din))) // 0 <= quantity < 1
      res = din;
   else begin // all other cases
      Bit#(TAdd#(m,3)) m = { 1'b1, din.sfd, din.round };
      m = m << (din.exp - fromInteger(bias(din)) + 1);
      res.exp = fromInteger(bias(din)) - 1;
      res = normalize(res, { 1'b0, m, 1'b0 });
   end
   return res;
endfunction

////////////////////////////////////////////////////////////////////////////////
/// Real type conversion
////////////////////////////////////////////////////////////////////////////////
instance RealLiteral#( FloatingPoint#(e,m) );
   function FloatingPoint#(e,m) fromReal( Real n );
      FloatingPoint#(e,m) out = defaultValue;
      Bit#(m) sfdm = 0; Bit#(2) round = 0; Bit#(53) rest = 0;
      
      let {s,ma,ex} = decodeReal(n);
   
      Bit#(53) sfd = s ? fromInteger(ma) : fromInteger(-ma);
      let msbindex = findIndexOneMSB_(sfd);
      let exp      = ex + msbindex - 1;

      if (msbindex == 0) begin 
	 out.sign   = !s;
	 out.exp    = 0;
	 out.sfd    = 0;
	 out.round  = 0;
	 out.sticky = 0;
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
	 { sfdm, round, rest } = unpack(cExtendLSB(sfd) >> (minexp(out) - exp - 1));
	 out.sfd        = sfdm;
	 out.round      = round;
	 out.sticky     = |rest;
      end
      else begin
      	 out.sign       = !s;
      	 Bit#(e) x      = fromInteger(exp) + fromInteger(bias(out));
      	 out.exp        = unpack(x);
	 { sfdm, round, rest } = unpack(cExtendLSB(sfd) << (53 - (msbindex - 1)));
	 out.sfd        = sfdm;
	 out.round      = round;
	 out.sticky     = |rest;
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
   
   function Bool inLiteralRange(a, n);
      return False;
   endfunction
endinstance


////////////////////////////////////////////////////////////////////////////////
/// Ord
////////////////////////////////////////////////////////////////////////////////
instance Ord#( FloatingPoint#(e,m) );
   function Bool \< ( FloatingPoint#(e,m) in1, FloatingPoint#(e,m) in2 );
      let signLT = (in1.sign && !in2.sign);
      let signEQ = in1.sign == in2.sign;
      let expLT  = in1.exp < in2.exp;
      let expEQ  = in1.exp == in2.exp;
      let manLT  = in1.sfd < in2.sfd;
      return ( signLT || (signEQ && expLT) || (signEQ && expEQ && manLT) );
   endfunction
   
   function Bool \<= ( FloatingPoint#(e,m) in1, FloatingPoint#(e,m) in2 );
      let signLT = (in1.sign && !in2.sign);
      let signEQ = in1.sign == in2.sign;
      let expLT  = in1.exp < in2.exp;
      let expEQ  = in1.exp == in2.exp;
      let manLT  = in1.sfd < in2.sfd;
      let manEQ  = in1.sfd == in2.sfd;
      return ( signLT || (signEQ && expLT) || (signEQ && expEQ && manLT) || (signEQ && expEQ && manEQ) );
   endfunction
   
   function Bool \> ( FloatingPoint#(e,m) in1, FloatingPoint#(e,m) in2 );
      let signGT = (!in1.sign && in2.sign);
      let signEQ = in1.sign == in2.sign;
      let expGT  = in1.exp > in2.exp;
      let expEQ  = in1.exp == in2.exp;
      let manGT  = in1.sfd > in2.sfd;
      return ( signGT || (signEQ && expGT) || (signEQ && expEQ && manGT) );
   endfunction
   
   function Bool \>= ( FloatingPoint#(e,m) in1, FloatingPoint#(e,m) in2 );
      let signGT = (!in1.sign && in2.sign);
      let signEQ = in1.sign == in2.sign;
      let expGT  = in1.exp > in2.exp;
      let expEQ  = in1.exp == in2.exp;
      let manGT  = in1.sfd > in2.sfd;
      let manEQ  = in1.sfd == in2.sfd;
      return ( signGT || (signEQ && expGT) || (signEQ && expEQ && manGT) || (signEQ && expEQ && manEQ) );
   endfunction
   
   function Ordering compare( FloatingPoint#(e,m) x, FloatingPoint#(e,m) y );
      let signLT = (x.sign && !y.sign);
      let signEQ = x.sign == y.sign;
      let signGT = (!x.sign && y.sign);
      let expLT  = x.exp < y.exp;
      let expEQ  = x.exp == y.exp;
      let expGT  = x.exp > y.exp;
      let manLT  = x.sfd < y.sfd;
      let manGT  = x.sfd > y.sfd;
      let manEQ  = x.sfd == y.sfd;
      
      if (signLT || (signEQ && expLT) || (signEQ && expEQ && manLT))      return LT;
      else if (signGT || (signEQ && expGT) || (signEQ && expEQ && manGT)) return GT;
      else return EQ;
   endfunction
   
   function FloatingPoint#(e,m) min( FloatingPoint#(e,m) x, FloatingPoint#(e,m) y );
      let signLT = (x.sign && !y.sign);
      let signEQ = x.sign == y.sign;
      let expLT  = x.exp < y.exp;
      let expEQ  = x.exp == y.exp;
      let manLT  = x.sfd < y.sfd;
   
      if (signLT || (signEQ && expLT) || (signEQ && expEQ && manLT)) return x;
      else return y;
   endfunction
   
   function FloatingPoint#(e,m) max( FloatingPoint#(e,m) x, FloatingPoint#(e,m) y );
      let signEQ = x.sign == y.sign;
      let signGT = (!x.sign && y.sign);
      let expEQ  = x.exp == y.exp;
      let expGT  = x.exp > y.exp;
      let manGT  = x.sfd > y.sfd;
   
      if (signGT || (signEQ && expGT) || (signEQ && expEQ && manGT)) return x;
      else return y;
   endfunction
   
endinstance

////////////////////////////////////////////////////////////////////////////////
/// Arith
////////////////////////////////////////////////////////////////////////////////
instance Arith#( FloatingPoint#(e,m) );
   function FloatingPoint#(e,m) \+ ( FloatingPoint#(e,m) in1, FloatingPoint#(e,m) in2 );
      return addFP(in1, in2);
   endfunction
   
   function FloatingPoint#(e,m) \- ( FloatingPoint#(e,m) in1, FloatingPoint#(e,m) in2 );
      in2.sign = !in2.sign;
      return addFP(in1, in2);
   endfunction
   
   function FloatingPoint#(e,m) negate (FloatingPoint#(e,m) in1 );
      in1.sign = !in1.sign;
      return in1;
   endfunction
   
   function FloatingPoint#(e,m) \* ( FloatingPoint#(e,m) in1, FloatingPoint#(e,m) in2 );
      return multFP(in1, in2);
   endfunction
   
   function FloatingPoint#(e,m) \/ ( FloatingPoint#(e,m) in1, FloatingPoint#(e,m) in2 );
      return divFP(in1, in2);
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
function FloatingPoint#(e,m) addFP ( FloatingPoint#(e,m) in1, FloatingPoint#(e,m) in2 );
   FloatingPoint#(e,m) a = defaultValue;
   FloatingPoint#(e,m) b = defaultValue;
   FloatingPoint#(e,m) out = defaultValue;
      
   Bit#(e) diffamt;
      
   if (in1.exp > in2.exp) begin // A > B
      a = in1;
      b = in2;
      diffamt = in1.exp - in2.exp;
   end
   else if (in2.exp > in1.exp) begin // B > A
      a = in2;
      b = in1;
      diffamt = in2.exp - in1.exp;
   end
   else if (in1.sfd > in2.sfd) begin // A > B
      a = in1;
      b = in2;
      diffamt = 0;
   end
   else begin // B >= A
      a = in2;
      b = in1;
      diffamt = 0;
   end
   
   out.sign = a.sign;
   out.exp  = a.exp;
   
   b = rightshift(b, diffamt);
   
   Bit#(1) hiddena = (a.exp == 0) ? 1'b0 : 1'b1;
   Bit#(1) hiddenb = ((b.exp == 0) || (diffamt != 0)) ? 1'b0 : 1'b1;
   
   // mantissa addition involves round bits, hidden bit, and an extra carry out bit (5 in total)
   Bit#(TAdd#(m,5)) opA = { 1'b0, hiddena, a.sfd, a.round, a.sticky };
   Bit#(TAdd#(m,5)) opB = { 1'b0, hiddenb, b.sfd, b.round, b.sticky };
   Bit#(TAdd#(m,5)) result;
   
   if (a.sign == b.sign) result = opA + opB;
   else                  result = opA - opB;
   
   // normalize the result.
   if (isNaN(in1) || isNaN(in2)) begin
      out = snan();
   end
   else if (isInfinity(in1) && isInfinity(in2)) begin
      out = (in1.sign == in2.sign) ? infinity(in1.sign) : snan();
   end
   else begin
      out = normalize( out, result );
      out = round_default(out);
   end

   return out;
endfunction

////////////////////////////////////////////////////////////////////////////////
/// Multiply
////////////////////////////////////////////////////////////////////////////////
function FloatingPoint#(e,m) multFP ( FloatingPoint#(e,m) in1, FloatingPoint#(e,m) in2 );
   FloatingPoint#(e,m) out = zero(False);
   
   // calculate the sign
   out.sign = in1.sign != in2.sign;
      
   // calculate the new exponent
   Int#(TAdd#(e,1)) exp1 = (in1.exp == 0) ? fromInteger(minexp(in1)-1) : signExtend(unpack(unbias(in1)));
   Int#(TAdd#(e,1)) exp2 = (in2.exp == 0) ? fromInteger(minexp(in2)-1) : signExtend(unpack(unbias(in2)));
   Int#(TAdd#(e,1)) newexp = exp1 + exp2 + fromInteger(bias(in2));
   out.exp = cExtend(newexp);
      
   // calculate the new significand
   Bit#(1) hidden1 = (in1.exp == 0) ? 1'b0 : 1'b1;
   Bit#(1) hidden2 = (in2.exp == 0) ? 1'b0 : 1'b1;
   
   Bit#(TAdd#(m,4)) opA = { hidden1, in1.sfd, in1.round, in1.sticky };
   Bit#(TAdd#(m,4)) opB = { hidden2, in2.sfd, in2.round, in2.sticky };
   
   Bit#(TAdd#(TAdd#(m,4),TAdd#(m,4))) sfdres = primMul(opA, opB);
   
   // normalize the significand
   if (isNaN(in1) || isNaN(in2)) begin
      out = snan();
   end
   else if ((isInfinity(in1) && isZero(in2)) || (isZero(in1) && isInfinity(in2))) begin
      out = snan();
   end
   else if (isInfinity(in1) || isInfinity(in2)) begin
      out = infinity(out.sign);
   end
   else begin
      out = normalize(out, sfdres);
      out = round_default(out);
   end
   
   return out;
endfunction

////////////////////////////////////////////////////////////////////////////////
/// Divide
////////////////////////////////////////////////////////////////////////////////
function FloatingPoint#(e,m) divFP ( FloatingPoint#(e,m) in1, FloatingPoint#(e,m) in2 );
   FloatingPoint#(e,m) out = defaultValue;

   // calculate the sign
   out.sign = in1.sign != in2.sign;
   
   // calculate the new exponent
   Int#(TAdd#(e,1)) exp1 = (in1.exp == 0) ? fromInteger(minexp(in1)-1) : signExtend(unpack(unbias(in1)));
   Int#(TAdd#(e,1)) exp2 = (in2.exp == 0) ? fromInteger(minexp(in2)-1) : signExtend(unpack(unbias(in2)));
   Bit#(e) shift = 0;
   if ((exp1 - exp2) < fromInteger(minexp(out)-1)) begin
      out.exp = 0;
      shift   = cExtend(fromInteger(minexp(out)-1) - (exp1 - exp2));
   end
   else begin
      Int#(TAdd#(e,1)) newexp = exp1 - exp2 + fromInteger(bias(in2));
      out.exp = cExtend(newexp);
   end

   // calculate the new significand
   Bit#(1) hidden1 = (in1.exp == 0) ? 1'b0 : 1'b1;
   Bit#(1) hidden2 = (in2.exp == 0) ? 1'b0 : 1'b1;

   // XXX
   Bit#(TAdd#(TAdd#(m,4),TAdd#(m,4))) opA = zExtendLSB({ 1'b0, hidden1, in1.sfd, in1.round, in1.sticky });
   Bit#(TAdd#(TAdd#(m,4),TAdd#(m,4))) opB = zExtend({ hidden2, in2.sfd, in2.round, in2.sticky });
   Bit#(TAdd#(TAdd#(m,4),TAdd#(m,4))) sfdres = opA/opB;
   Bit#(TAdd#(m,5)) rsfd = cExtend(sfdres >> shift);
   
   // normalize the result
   if (isNaN(in1) || isNaN(in2)) begin
      out = snan();
   end
   else if (isInfinity(in1) && isInfinity(in2)) begin
      out = snan();
   end
   else if (isInfinity(in1)) begin
      out = infinity(out.sign);
   end
   else if (isInfinity(in2)) begin
      out = zero(out.sign);
   end
   else if (isZero(in2)) begin
      out = (isZero(in1)) ? snan() : infinity(out.sign);
   end
   else begin
      out = normalize(out, rsfd);
      out = round_default(out);
   end
   
   return out;
endfunction

////////////////////////////////////////////////////////////////////////////////
/// Pipelined Floating Point Adder
////////////////////////////////////////////////////////////////////////////////
module mkFloatingPointAdder(Server#(Tuple2#(FloatingPoint#(e,m), FloatingPoint#(e,m)), FloatingPoint#(e,m)));

   ////////////////////////////////////////////////////////////////////////////////
   /// S0
   ////////////////////////////////////////////////////////////////////////////////
   FIFO#(Tuple2#(FloatingPoint#(e,m),
		 FloatingPoint#(e,m)))       fOperands_S0        <- mkLFIFO;

   ////////////////////////////////////////////////////////////////////////////////
   /// S1 - subtract exponents
   ////////////////////////////////////////////////////////////////////////////////
   FIFO#(FloatingPoint#(e,m))                fOperandA_S1        <- mkLFIFO;
   FIFO#(FloatingPoint#(e,m))                fOperandB_S1        <- mkLFIFO;
   FIFO#(Bit#(e))                            fExp_S1             <- mkLFIFO;
   FIFO#(Bit#(e))                            fExpDiff_S1         <- mkLFIFO;
   
   rule s1_stage;
      let ops <- toGet(fOperands_S0).get;
      match { .opA, .opB } = ops;
      
      if (opA.exp > opB.exp) begin
	 fExp_S1.enq(opA.exp);
	 fExpDiff_S1.enq(opA.exp - opB.exp);
	 fOperandA_S1.enq(opA);
	 fOperandB_S1.enq(opB);
      end
      else if (opB.exp > opA.exp) begin
	 fExp_S1.enq(opB.exp);
	 fExpDiff_S1.enq(opB.exp - opA.exp);
	 fOperandA_S1.enq(opB);
	 fOperandB_S1.enq(opA);
      end
      else if (opA.sfd > opB.sfd) begin
	 fExp_S1.enq(opA.exp);
	 fExpDiff_S1.enq(0);
	 fOperandA_S1.enq(opA);
	 fOperandB_S1.enq(opB);
      end
      else begin
	 fExp_S1.enq(opB.exp);
	 fExpDiff_S1.enq(0);
	 fOperandA_S1.enq(opB);
	 fOperandB_S1.enq(opA);
      end
   endrule

   ////////////////////////////////////////////////////////////////////////////////
   /// S2 - align significands
   ////////////////////////////////////////////////////////////////////////////////
   FIFO#(FloatingPoint#(e,m))                fOperandA_S2        <- mkLFIFO;
   FIFO#(FloatingPoint#(e,m))                fOperandB_S2        <- mkLFIFO;
   FIFO#(Bool)                               fSign_S2            <- mkLFIFO;
   FIFO#(Bit#(e))                            fExp_S2             <- mkLFIFO;
   FIFO#(Bit#(e))                            fExpDiff_S2         <- mkLFIFO;
   
   rule s2_stage;
      let opA <- toGet(fOperandA_S1).get;
      let opB <- toGet(fOperandB_S1).get;
      let exp <- toGet(fExp_S1).get;
      let diff <- toGet(fExpDiff_S1).get;
      
      opB = rightshift(opB, diff);
      
      fOperandA_S2.enq(opA);
      fOperandB_S2.enq(opB);
      fSign_S2.enq(opA.sign);
      fExp_S2.enq(exp);
      fExpDiff_S2.enq(diff);
   endrule

   ////////////////////////////////////////////////////////////////////////////////
   /// S3 - add/subtract significands
   ////////////////////////////////////////////////////////////////////////////////
   FIFO#(Bit#(TAdd#(m,5)))                   fAddResult_S3       <- mkLFIFO;
   FIFO#(Bit#(TAdd#(m,5)))                   fSubResult_S3       <- mkLFIFO;
   FIFO#(Bool)                               fSign_S3            <- mkLFIFO;
   FIFO#(Bool)                               fSignDiff_S3        <- mkLFIFO;
   FIFO#(Bit#(e))                            fExp_S3             <- mkLFIFO;
   FIFO#(Bool)                               fNaN_S3             <- mkLFIFO;
   FIFO#(Bool)                               fInf_S3             <- mkLFIFO;
   
   rule s3_stage;
      let opA <- toGet(fOperandA_S2).get;
      let opB <- toGet(fOperandB_S2).get;
      let sign <- toGet(fSign_S2).get;
      let exp <- toGet(fExp_S2).get;
      let diff <- toGet(fExpDiff_S2).get;
      
      Bit#(1) hiddenA = (opA.exp == 0) ? 0 : 1;
      Bit#(1) hiddenB = ((opB.exp == 0) || (diff != 0)) ? 0 : 1;
      
      Bit#(TAdd#(m,5)) a = { 1'b0, hiddenA, opA.sfd, opA.round, opA.sticky };
      Bit#(TAdd#(m,5)) b = { 1'b0, hiddenB, opB.sfd, opB.round, opB.sticky };
      
      fAddResult_S3.enq(a + b);
      fSubResult_S3.enq(a - b);
      fSign_S3.enq(sign);
      fSignDiff_S3.enq(opA.sign == opB.sign);
      fExp_S3.enq(exp);
      fNaN_S3.enq(isNaN(opA) || isNaN(opB) || (isInfinity(opA) && isInfinity(opB) && (opA.sign != opB.sign)));
      fInf_S3.enq(isInfinity(opA) && isInfinity(opB) && (opA.sign == opB.sign));
   endrule
   
   ////////////////////////////////////////////////////////////////////////////////
   /// S4 - normalize
   ////////////////////////////////////////////////////////////////////////////////
   FIFO#(FloatingPoint#(e,m))                fResult_S4          <- mkLFIFO;
   FIFO#(Bool)                               fNaN_S4             <- mkLFIFO;
   FIFO#(Bool)                               fInf_S4             <- mkLFIFO;
   
   rule s4_stage;
      let addres <- toGet(fAddResult_S3).get;
      let subres <- toGet(fSubResult_S3).get;
      let sign   <- toGet(fSign_S3).get;
      let signdiff <- toGet(fSignDiff_S3).get;
      let exp    <- toGet(fExp_S3).get;
      let nan    <- toGet(fNaN_S3).get;
      let inf    <- toGet(fInf_S3).get;
      
      Bit#(TAdd#(m,5)) result;
      
      if (signdiff) result = addres;
      else          result = subres;
      
      FloatingPoint#(e,m) out = defaultValue;
      
      if (nan)      out = snan();
      else if (inf) out = infinity(sign);
      else begin
	 out.sign = sign;
	 out.exp = exp;
	 out = normalize(out, result);
      end
      
      fResult_S4.enq(out);
      fNaN_S4.enq(nan);
      fInf_S4.enq(inf);
   endrule
   
   ////////////////////////////////////////////////////////////////////////////////
   /// S5 - round result
   ////////////////////////////////////////////////////////////////////////////////
   FIFO#(FloatingPoint#(e,m))                fResult_S5          <- mkLFIFO;
   
   rule s5_stage;
      let result <- toGet(fResult_S4).get;
      let nan    <- toGet(fNaN_S4).get;
      let inf    <- toGet(fInf_S4).get;
      
      FloatingPoint#(e,m) out = result;
      
      if (!nan && !inf) begin
	 out = round_default(out);
      end
      
      fResult_S5.enq(out);
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
module mkFloatingPointMultiplier(Server#(Tuple2#(FloatingPoint#(e,m), FloatingPoint#(e,m)), FloatingPoint#(e,m)))
   provisos(  Add#(_1, TAdd#(m,4), TMul#(TDiv#(TAdd#(m,4), 17), 17))
            , Add#(_2, TAdd#(m,4), TMul#(TDiv#(TAdd#(m,4), 24), 24))
            , Add#(TDiv#(TMul#(TDiv#(TAdd#(m, 4), 24), TDiv#(TAdd#(m, 4), 17)), 2), _3, TMul#(TDiv#(TAdd#(m, 4), 24), TDiv#(TAdd#(m, 4), 17)))
	    , VectorTreeReduce#(TExp#(TLog#(TMul#(TDiv#(TAdd#(m, 4), 24), TDiv#(TAdd#(m, 4), 17)))), Bit#(TAdd#(TAdd#(m, 4), TAdd#(m, 4))))
            );
               
   ////////////////////////////////////////////////////////////////////////////////
   /// S0
   ////////////////////////////////////////////////////////////////////////////////
   FIFO#(Tuple2#(FloatingPoint#(e,m),
                 FloatingPoint#(e,m)))       fOperands_S0        <- mkLFIFO;

   Server#(Tuple2#(Bit#(TAdd#(m,4)), 
                   Bit#(TAdd#(m,4))),
           Bit#(TAdd#(TAdd#(m,4),TAdd#(m,4)))) mMult             <- mkGeneralPipelinedMultiplier;
  
   ////////////////////////////////////////////////////////////////////////////////
   /// S1 - calculate the new exponent/sign
   ////////////////////////////////////////////////////////////////////////////////
   FIFO#(Bit#(TAdd#(m,4)))                   fOpASfd_S1          <- mkLFIFO;
   FIFO#(Bit#(TAdd#(m,4)))                   fOpBSfd_S1          <- mkLFIFO;
   FIFO#(Int#(TAdd#(e,1)))                   fExp_S1             <- mkLFIFO;
   FIFO#(Bool)                               fSign_S1            <- mkLFIFO; 
   FIFO#(Bool)                               fNaN_S1             <- mkLFIFO;
   FIFO#(Bool)                               fInf_S1             <- mkLFIFO;
  
   rule s1_stage;
      let ops <- toGet(fOperands_S0).get;
      match { .opA, .opB } = ops;

      Int#(TAdd#(e,1)) expA = (opA.exp == 0) ? fromInteger(minexp(opA)-1) : signExtend(unpack(unbias(opA)));
      Int#(TAdd#(e,1)) expB = (opB.exp == 0) ? fromInteger(minexp(opB)-1) : signExtend(unpack(unbias(opB)));
      Int#(TAdd#(e,1)) newexp = expA + expB + fromInteger(bias(opB));
      fExp_S1.enq(newexp);
      
      fSign_S1.enq(opA.sign != opB.sign);

      Bit#(TAdd#(m,4)) opAsfd = { (opA.exp == 0) ? 1'b0 : 1'b1, opA.sfd, opA.round, opA.sticky };
      Bit#(TAdd#(m,4)) opBsfd = { (opB.exp == 0) ? 1'b0 : 1'b1, opB.sfd, opB.round, opB.sticky };
      
      fOpASfd_S1.enq(opAsfd);
      fOpBSfd_S1.enq(opBsfd);
      
      fNaN_S1.enq((isNaN(opA) || isNaN(opB)) || ((isInfinity(opA) && isZero(opB)) || (isZero(opA) && isInfinity(opB))));
      fInf_S1.enq((isInfinity(opA) && !isZero(opB)) || (isInfinity(opB) && !isZero(opA)));
   endrule
   
   ////////////////////////////////////////////////////////////////////////////////
   /// S2
   ////////////////////////////////////////////////////////////////////////////////
   FIFO#(Bit#(TAdd#(TAdd#(m,4),TAdd#(m,4)))) fSfdRes_S2          <- mkLFIFO;
   FIFO#(Int#(TAdd#(e,1)))                   fExp_S2             <- mkLFIFO;
   FIFO#(Bool)                               fSign_S2            <- mkLFIFO;
   FIFO#(Bool)                               fNaN_S2             <- mkLFIFO;
   FIFO#(Bool)                               fInf_S2             <- mkLFIFO;
   
   rule s2_stage;
      let opAsfd <- toGet(fOpASfd_S1).get;
      let opBsfd <- toGet(fOpBSfd_S1).get;
      let exp    <- toGet(fExp_S1).get;
      let sign   <- toGet(fSign_S1).get;
      let nan    <- toGet(fNaN_S1).get;
      let inf    <- toGet(fInf_S1).get;

      mMult.request.put(tuple2(opAsfd, opBsfd));
      
      fExp_S2.enq(exp);
      fSign_S2.enq(sign);
      fNaN_S2.enq(nan);
      fInf_S2.enq(inf);
   endrule
   
   (* fire_when_enabled *)
   rule s2_stage_done;
      let response <- mMult.response.get;
      fSfdRes_S2.enq(response);
   endrule
   
   ////////////////////////////////////////////////////////////////////////////////
   /// S3
   ////////////////////////////////////////////////////////////////////////////////
   FIFO#(Bit#(TAdd#(TAdd#(m,4),TAdd#(m,4)))) fSfdRes_S3          <- mkLFIFO;
   FIFO#(Int#(TAdd#(e,1)))                   fExp_S3             <- mkLFIFO;
   FIFO#(Bool)                               fSign_S3            <- mkLFIFO;
   FIFO#(Bool)                               fNaN_S3             <- mkLFIFO;
   FIFO#(Bool)                               fInf_S3             <- mkLFIFO;
   
   rule s3_stage;
      let result <- toGet(fSfdRes_S2).get;
      let exp    <- toGet(fExp_S2).get;
      let sign   <- toGet(fSign_S2).get;
      let nan    <- toGet(fNaN_S2).get;
      let inf    <- toGet(fInf_S2).get;
      
      fSfdRes_S3.enq(result);
      fExp_S3.enq(exp);
      fSign_S3.enq(sign);
      fNaN_S3.enq(nan);
      fInf_S3.enq(inf);
   endrule
   
   ////////////////////////////////////////////////////////////////////////////////
   /// S4
   ////////////////////////////////////////////////////////////////////////////////
   FIFO#(FloatingPoint#(e,m))                fResult_S4          <- mkLFIFO;
   FIFO#(Bool)                               fNaN_S4             <- mkLFIFO;
   FIFO#(Bool)                               fInf_S4             <- mkLFIFO;

   rule s4_stage;
      let sfdres <- toGet(fSfdRes_S3).get;
      let exp    <- toGet(fExp_S3).get;
      let sign   <- toGet(fSign_S3).get;
      let nan    <- toGet(fNaN_S3).get;
      let inf    <- toGet(fInf_S3).get;

      FloatingPoint#(e,m) result = defaultValue;
      if (nan)       result = snan();
      else if (inf)  result = infinity(sign);
      else begin
	 result.exp = cExtend(exp);
	 result.sign = sign;
	 result = normalize(result, sfdres);
      end
      
      fResult_S4.enq(result);
      fNaN_S4.enq(nan);
      fInf_S4.enq(inf);
   endrule

   ////////////////////////////////////////////////////////////////////////////////
   /// S5
   ////////////////////////////////////////////////////////////////////////////////
   FIFO#(FloatingPoint#(e,m))                fResult_S5          <- mkLFIFO;
   
   rule s5_stage;
      let result <- toGet(fResult_S4).get;
      let nan    <- toGet(fNaN_S4).get;
      let inf    <- toGet(fInf_S4).get;
      
      FloatingPoint#(e,m) out = result;
      
      if (!nan && !inf) begin
	 out = round_default(out);
      end
      
      fResult_S5.enq(out);
   endrule
   
   ////////////////////////////////////////////////////////////////////////////////
   /// Interface Connections / Methods
   ////////////////////////////////////////////////////////////////////////////////
   interface request = toPut(fOperands_S0);
   interface response = toGet(fResult_S5);

endmodule: mkFloatingPointMultiplier


// The output of a Pipe component is the output subset of the FIFOF interface,
// with the same semantics
interface PipeOut#(type t);
   method t      first();
   method Action deq();
   method Bool   notEmpty();
endinterface

// A Pipe component is a module with a PipeOut parameter and a PipeOut interface
// i.e., a function from PipeOut to Module#(PipeOut)
typedef (function m#(PipeOut #(tb)) mkFoo (PipeOut#(ta) ifc)) Pipe#(type m, type ta, type tb);
    
	    
typeclass VectorTreeReduce#(numeric type n, type a);
   module mkTreeReducePipe (  Pipe#(module, Tuple2#(a,a), a)  reducepipe
			    , Bit#(32)                addBuffer
			    , PipeOut#(Vector#(n, a)) pipeIn
			    , PipeOut#(a)             ifc
			    );
   module mkTreeReduceFn   (  function a              reduce2(a x, a y)
			    , function a              reduce1(a x)
			    , Bit#(32)                addBuffer
			    , PipeOut#(Vector#(n, a)) pipeIn
			    , PipeOut#(a)             ifc
			    );
endtypeclass

instance VectorTreeReduce#(1, a)
   provisos( Bits#(a, sa) );
   
   module mkTreeReducePipe (  Pipe#(module, Tuple2#(a,a), a)  reducepipe
			    , Bit#(32)                addBuffer
			    , PipeOut#(Vector#(1, a)) pipeIn
			    , PipeOut#(a)             ifc
			    );
      (* hide *)
      let _vreduce1 <- mkFn_to_Pipe( head, pipeIn );
      return _vreduce1;
   endmodule
   
   module mkTreeReduceFn   (  function a              reduce2(a x, a y)
			    , function a              reduce1(a x)
			    , Bit#(32)                addBuffer
			    , PipeOut#(Vector#(1, a)) pipeIn
			    , PipeOut#(a)             ifc
			    )
      provisos( Bits#(a, sa) );
   
      (* hide *)
      let _vTreeReduce1 <- mkFn_to_Pipe( head, pipeIn );
      return _vTreeReduce1;
   endmodule
endinstance
	    
instance VectorTreeReduce#(2, a)
   provisos( Bits#(a ,sa) );

   module          mkTreeReducePipe (  Pipe#(module, Tuple2#(a,a), a)  reducepipe
				     , Bit#(32)                addBuffer
				     , PipeOut#(Vector#(2, a)) pipeIn
				     , PipeOut#(a)             ifc
				     );
      let err = error("Impossible error in Tree reduction 2");
      (* hide *)
      PipeOut#(Tuple2#(a, a)) _paired <- mkFn_to_Pipe(compose(head, mapPairs(tuple2, err)), pipeIn);
      PipeOut#(a)             map2to1 <- reducepipe(_paired);
      let buffer1 = map2to1;
      
      if (addBuffer[0] == 1) begin
	 buffer1 <- mkBuffer(buffer1);
      end
      
      return buffer1;
   endmodule
   
   module mkTreeReduceFn   (  function a              reduce2(a x, a y)
			    , function a              reduce1(a x)
			    , Bit#(32)                addBuffer
			    , PipeOut#(Vector#(2, a)) pipeIn
			    , PipeOut#(a)             ifc
			    )
      provisos( Bits#(a, sa) );
   
      let vTreeReduceFinal <- mkFn_to_Pipe_Buffered(  False
						    , compose(head, (mapPairs (reduce2, reduce1)))
						    , addBuffer[0] == 1
						    , pipeIn
						    );
      return vTreeReduceFinal;
   endmodule
   
endinstance

	    	    
instance VectorTreeReduce#(n, a)
   provisos(  Bits#(a ,sa)
	    , Div#(n, 2, n2)
	    , VectorTreeReduce#(n2, a)
	    );

   module mkTreeReducePipe (  Pipe#(module, Tuple2#(a,a), a)  reducepipe
			    , Bit#(32)                addBuffer
			    , PipeOut#(Vector#(n, a)) pipeIn
			    , PipeOut#(a)             ifc
			    );
      let err = error("Error in mkTreeReducePipe -- size of input pipe vector must be a power of 2");
      (* hide *)
      let _paired <- mkFn_to_Pipe(mapPairs(tuple2, err), pipeIn);
      let mapN2 <- mkMap(reducepipe, _paired);
      let bufferN2 = mapN2;
      
      if (addBuffer[0] == 1) begin
	 bufferN2 <- mkBuffer(bufferN2);
      end
      
      let vTreeReduceN2 <- mkTreeReducePipe(reducepipe, addBuffer>>1, bufferN2);
      return vTreeReduceN2;
   endmodule
   
   module mkTreeReduceFn   (  function a              reduce2(a x, a y)
			    , function a              reduce1(a x)
			    , Bit#(32)                addBuffer
			    , PipeOut#(Vector#(n, a)) pipeIn
			    , PipeOut#(a)             ifc
			    );
      PipeOut#(Vector#(n2, a)) reduceFnNtoN2 <- mkFn_to_Pipe_Buffered(  False
								      , mapPairs(reduce2, reduce1)
								      , addBuffer[0] == 1
								      , pipeIn
								      );
					  
      PipeOut#(a) vTreeReduceN2 <- mkTreeReduceFn(reduce2, reduce1, (addBuffer >> 1), reduceFnNtoN2);
      return vTreeReduceN2;
   endmodule
   
endinstance

////////////////////////////////////////////////////////////////////////////////
/// Functions / Modules
////////////////////////////////////////////////////////////////////////////////
function PipeOut#(a) f_FIFOF_to_PipeOut (FIFOF#(a) fifof);
   return (interface PipeOut;
	      method a first();
		 return fifof.first;
	      endmethod
	      method Action deq();
		 fifof.deq;
	      endmethod
	      method Bool notEmpty();
		 return fifof.notEmpty();
	      endmethod
	   endinterface);
endfunction
      
module mkFn_to_Pipe#(function tb fn (ta x), PipeOut#(ta) po_in)(PipeOut#(tb));
   method tb first();
      return fn(po_in.first);
   endmethod
			
   method Action deq();
      po_in.deq;
   endmethod
			
   method Bool notEmpty();
      return po_in.notEmpty;
   endmethod			
endmodule
	    
module mkBuffer#(PipeOut#(a) po_in)(PipeOut#(a))
   provisos( Bits#(a, sa) );
   
   FIFOF#(a)   fifof   <- mkLFIFOF;
   
   rule rl_into_buffer;
      fifof.enq(po_in.first);
      po_in.deq;
   endrule
   
   return f_FIFOF_to_PipeOut(fifof);
endmodule
   
module mkFn_to_Pipe_Buffered#(  Bool param_buf_before
			      , function b fn (a x)
			      , Bool param_buf_after
			      , PipeOut #(a) po_in)(PipeOut #(b))
   provisos (  Bits #(a, sa)
	     , Bits #(b, sb)
	     );

   PipeOut #(a) preFIFO = po_in;

   if (param_buf_before)
      preFIFO <- mkBuffer (po_in);

   PipeOut #(b) postFIFO <- mkFn_to_Pipe (fn, preFIFO);

   if (param_buf_after)
      postFIFO <- mkBuffer (postFIFO);

   return postFIFO;
endmodule

module mkMap#(Pipe#(module, a,b) mkP, PipeOut#(Vector#(n, a)) po_in)(PipeOut#(Vector#(n, b)))
   provisos( Bits#(a, sa) );
   
   Vector#(n, FIFO#(Bit#(0))) mkMapTakenMarkers <- replicateM(mkBypassFIFO);
   
   rule rl_deq;
      po_in.deq;
      for(Integer j = 0; j < valueof(n); j = j + 1)
	 mkMapTakenMarkers[j].deq;
   endrule
   
   function PipeOut#(a) genIfc(Integer j);
      return (interface PipeOut;
		 method a first();
		    return po_in.first[j];
		 endmethod
		 method Action deq();
		    mkMapTakenMarkers[j].enq(?);
		 endmethod
		 method Bool notEmpty();
		    return ?; // don't care
		 endmethod
	      endinterface);
   endfunction
   
   Vector#(n, PipeOut#(b)) mkMapPipeElem <- mapM(mkP, map(genIfc, genVector));
   
   method Vector#(n, b) first();
      function b get_first(PipeOut#(b) po) = po.first();
      return map(get_first, mkMapPipeElem);
   endmethod
   
   method Action deq;
      for(Integer j = 0; j < valueof(n); j = j + 1)
	 mkMapPipeElem[j].deq;
   endmethod
   
   method Bool notEmpty();
      return po_in.notEmpty();
   endmethod
   
endmodule

// mkGeneralPipelinedMultiplier 
//  - The design of this module is somewhat wasteful at the moment and could be optimized to remove 
//    extra registers and to remove the need for register retiming.  However, most modern synthesis 
//    tools do a good job of both aspects, so for now, there is some fat in this module.
//
//  - The algorithm is quite simple and could be improved upon as well.  The idea is to break up the
//    multiplication into 25x18 multiplies and perform the sums over a sequence of clocks to prevent
//    a large multiple term addition.  To prevent signed multiplication, which can be more expensive
//    (clock rate) than unsigned, the 25x18 terms are padded to be 24x17 instead.  The 24x17 multiplies
//    infer FPGA 25x18 multipliers in parallel.  The partial products are then shifted into the proper
//    bit position for the subsequent summation.  The summation occurs over log2(n) cycles where n 
//    represents the number of partial products computed.  The result is then pipelined through 3-
//    stages to give the synthesis tool an opportunity to pipeline the summation process.
//    
module mkGeneralPipelinedMultiplier(Server#(Tuple2#(Bit#(a), Bit#(a)), Bit#(a2)))
   provisos(  Add#(1, _, a)            // make sure the SFD is not zero bits
            , Div#(a, 24, w)           // Compute the array multiplier width
            , Div#(a, 17, h)           // Compute the array multiplier height
            , Add#(a, a, a2)           // Compute the width of the result
            , Mul#(w, h, p)            // Compute the total number of product terms
            , Add#(_1, a, TMul#(h,17)) // Make sure the vector of Bit#(17)s is padded 
            , Add#(_2, a, TMul#(w,24)) // Make sure the vector of Bit#(24)s is padded
            , Log#(a2, la2)            // # of bits to represent an index into the result (used for shifting on partial product computation)
            , Log#(p, stages)          // compute the number of stages required to sum the partial products
	    , NumAlias#(p2, TExp#(stages))
            , Add#(stages, 1, d)       // depth of sum array
            , Add#(TDiv#(p,2), _3, p)  // *requested by the compiler
	    , VectorTreeReduce#(p2, Bit#(a2))
            );

   ////////////////////////////////////////////////////////////////////////////////
   /// Inputs
   ////////////////////////////////////////////////////////////////////////////////
   Reg#(Bit#(a))                  rOpA           <- mkRegU;
   Reg#(Bit#(a))                  rOpB           <- mkRegU;
   Reg#(Bool)                     rValid_S0      <- mkDReg(False);

   ////////////////////////////////////////////////////////////////////////////////
   /// S0 - parallel multiply
   ////////////////////////////////////////////////////////////////////////////////      
   Vector#(p, Reg#(Bit#(41)))     vrProducts     <- replicateM(mkRegU);
   Reg#(Bool)                     rValid_S1      <- mkReg(False);
   Vector#(p, UInt#(la2))         vShifts         = newVector;
          
   for(Integer i = 0; i < valueOf(h); i = i + 1) begin
      for(Integer j = 0; j < valueOf(w); j = j + 1) begin
         vShifts[(i*valueOf(w))+j] = (fromInteger(i)*17)+(fromInteger(j)*24);
      end
   end
            
   (* fire_when_enabled, no_implicit_conditions *)
   rule stage_0;
      Vector#(w, Bit#(24)) vOpA = unpack(zeroExtend(rOpA));
      Vector#(h, Bit#(17)) vOpB = unpack(zeroExtend(rOpB));
      Vector#(p, Bit#(41)) vProducts = replicate(0);

      for(Integer i = 0; i < valueof(h); i = i + 1) begin
         for(Integer j = 0; j < valueof(w); j = j + 1) begin
            vProducts[(i*valueOf(w))+j] = primMul(vOpA[j], vOpB[i]);
         end
      end
      
      writeVReg(vrProducts, vProducts);
      rValid_S1 <= rValid_S0;
   endrule
   
   ////////////////////////////////////////////////////////////////////////////////
   /// S1 - shift 
   ////////////////////////////////////////////////////////////////////////////////
   FIFOF#(Vector#(p2, Bit#(a2)))    fPartials      <- mkLFIFOF;

   rule stage_1(rValid_S1);
      Vector#(p2, Bit#(a2)) sumStart = replicate(0);
      for(Integer i = 0; i < valueOf(p); i = i + 1) begin
	 sumStart[i] = zExtend(readVReg(vrProducts)[i]) << vShifts[i];
      end
      
      fPartials.enq(sumStart);
   endrule
   
   ////////////////////////////////////////////////////////////////////////////////
   /// Adder Tree Stages
   ////////////////////////////////////////////////////////////////////////////////
   PipeOut#(Bit#(a2))             mAdderTree     <- mkTreeReduceFn(\+ , id, '1, f_FIFOF_to_PipeOut(fPartials));

   ////////////////////////////////////////////////////////////////////////////////
   /// Sn-2 stage for register rebalancing
   ////////////////////////////////////////////////////////////////////////////////
   Reg#(Bit#(a2))                 rResult_Sn2    <- mkRegU;
   Reg#(Bool)                     rValid_Sn2     <- mkReg(False);

   rule stage_nm2;
      let result = mAdderTree.first; mAdderTree.deq;
      rResult_Sn2 <= result;
      rValid_Sn2  <= True;
   endrule
   
   (* preempts = "stage_nm2, stage_nm2_idle" *)
   rule stage_nm2_idle;
      rValid_Sn2 <= False;
   endrule
            
   ////////////////////////////////////////////////////////////////////////////////
   /// Sn-1 stage for register rebalancing
   ////////////////////////////////////////////////////////////////////////////////
   Reg#(Bit#(a2))                 rResult_Sn1    <- mkRegU;
   Reg#(Bool)                     rValid_Sn1     <- mkReg(False);

   (* fire_when_enabled, no_implicit_conditions *)
   rule stage_nm1;
      rResult_Sn1 <= rResult_Sn2;
      rValid_Sn1  <= rValid_Sn2;
   endrule
            
   ////////////////////////////////////////////////////////////////////////////////
   /// Sn stage for register rebalancing
   ////////////////////////////////////////////////////////////////////////////////
   Reg#(Bit#(a2))                 rResult_Sn     <- mkRegU;
   Reg#(Bool)                     rValid_Sn      <- mkReg(False);

   (* fire_when_enabled, no_implicit_conditions *)
   rule stage_n;
      rResult_Sn <= rResult_Sn1;
      rValid_Sn  <= rValid_Sn1;
   endrule
            
   ////////////////////////////////////////////////////////////////////////////////
   /// Interface Connections / Methods
   ////////////////////////////////////////////////////////////////////////////////
   interface Put request;
      method Action put(Tuple2#(Bit#(a), Bit#(a)) x);
         match { .a, .b } = x;
         rOpA <= a;
         rOpB <= b;
         rValid_S0 <= True;
      endmethod
   endinterface
   
   interface Get response;
      method ActionValue#(Bit#(a2)) get if (rValid_Sn);
         return rResult_Sn;
      endmethod
   endinterface
            
endmodule

endpackage: FloatingPoint
