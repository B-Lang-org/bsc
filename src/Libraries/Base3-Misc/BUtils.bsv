package BUtils;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

import Vector::*;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

function a grab_left(b value)
   provisos(Bits#(a, sa), Bits#(b, sb), Add#(x, sa, sb));

   let result = truncate(pack(value) >> fromInteger((valueOf(sb) - valueOf(sa))));

   return unpack(result);
endfunction

function a reverse_bytes (a value)
      provisos (Bits#(a, sa), Add#(8, ignore, sa), Add#(8, sa, sb));

      Bit#(sa) result_bits = 0;
      Bit#(sa) value_bits = pack(value);
      Bit#(8)  one_byte = 0;
      Bit#(sb) z = 0;

      for (Integer x = (valueOf(sa) - 1); x > 0; x = x - 8)
	 begin
	    Nat y = fromInteger(x);
	    one_byte = value_bits[y:(y - 7)];
	    z = {one_byte, result_bits};
	    result_bits = grab_left(z);
	 end

      return unpack(result_bits);

endfunction

function Integer getSizeOf(a value)
   provisos(Bits#(a, sa));
   return valueOf(sa);
endfunction

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

function Bit#(m) zExtend(Bit#(n) value)
   provisos(Add#(n,m,k));
   Bit#(k) out = zeroExtend(value);
   if (valueOf(m) == 0)
      return ?;
   else
      return out[valueOf(m) - 1:0];
endfunction

function Bit#(m) sExtend(Bit#(n) value)
   provisos(Add#(n,m,k));
   Bit#(k) out = signExtend(value);
   if (valueOf(m) == 0)
      return ?;
   else
      return out[valueOf(m) - 1:0];
endfunction

function a cExtend(b value)
   provisos(Bits#(a, sa), Bits#(b, sb));

   let out = unpack(zExtend(pack(value)));

   return out;
endfunction

function Bit#(m) zExtendLSB(Bit#(n) value)
   provisos( Add#(n,m,k) );
   Bit#(k) out = { value, 0 };
   if (valueOf(m) == 0)
      return ?;
   else
      return out[valueof(k)-1:valueof(n)];
endfunction

function a cExtendLSB(b value)
   provisos( Bits#(a,sa), Bits#(b,sb) );
   let out = unpack(zExtendLSB(pack(value)));
   return out;
endfunction

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

function Bit#(size) getIndex (Vector#(count, Bool) vector)
   provisos (Log#(count, size));

   let icount = valueOf(count);

   Integer selected = 0;

   for (Integer x = 0; x < icount; x = x + 1)
      if (vector[x]) selected = x;

   return fromInteger(selected);
endfunction


////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

function Action dummyAction ();
   action
      $write("");
   endaction
endfunction


////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

typedef Bit#(TLog#(TAdd#(m, 1)))  LBit#(numeric type m);
typedef UInt#(TLog#(TAdd#(m, 1))) LUInt#(numeric type m);

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

function Bit#(m) duplicate(Bit#(n) d) provisos(Mul#(n,x,m));
   function Bit#(n) setVal(Integer i) = d;
   Vector#(x,Bit#(n)) v = map(setVal, genVector);
   return pack(v);
endfunction


endpackage
