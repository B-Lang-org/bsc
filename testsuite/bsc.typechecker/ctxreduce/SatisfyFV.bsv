package SatisfyFV;

import Vector::*;
import FixedPoint::*;

function FixedPoint#(i,rf) roundLSBs(FixedPoint#(i,f) a)
   provisos(Add#(i,f,a_sz), Add#(i,rf,r_sz), Add#(_,r_sz,a_sz));
   let n = _toInternal(a);
   let s = valueOf(a_sz) - valueOf(r_sz);
   Int#(r_sz) v = truncate(n >> s);
   Bool add_one = (pack(n)[s-1] == 1);
   return _fromInternal(add_one ? (v+1) : v);
endfunction: roundLSBs

// Lookup values in a pair of tables and perform linear interpolation
function FixedPoint#(ri,rf) linear_interp(Vector#(n,FixedPoint#(vi,f)) lut_even,
				 	  Vector#(n,FixedPoint#(vi,f)) lut_odd,
					  FixedPoint#(ri,f) last,
					  t x)
   provisos(Min#(vi, 1, 1),
            Log#(n,idx_bits), Bits#(t,t_sz),
            Add#(1, idx_bits, idx_bits2), Add#(idx_bits2,frac_bits,t_sz),
	    Add#(1,vi,ri), Add#(1,rf,rf_plus_1),
	    Arith#(FixedPoint#(ri,rf_plus_1)),
	    Add#(_2, frac_bits, rf_plus_1),
	    Add#(_5, f, rf_plus_1));
   let bits = pack(x);
   let msb = valueOf(t_sz) - 1;
   let lsb = valueOf(t_sz) - valueOf(idx_bits);
   UInt#(idx_bits) idx = unpack(bits[msb:lsb]);
   Bool odd = unpack(bits[lsb-1]);
   FixedPoint#(1,frac_bits) frac = unpack(bits[lsb-2:0]);
   FixedPoint#(ri,rf_plus_1) mix = fxptZeroExtend(frac);
   FixedPoint#(ri,rf_plus_1) out0 = ?;
   FixedPoint#(ri,rf_plus_1) out1 = ?;
   if (odd)
   begin
      out0 = fxptSignExtend(lut_odd[idx]);
      out1 = (idx == fromInteger(valueOf(n) - 1)) ?
             fxptSignExtend(last) :
             fxptSignExtend(lut_even[idx+1]);
   end
   else
   begin
      out0 = fxptSignExtend(lut_even[idx]);
      out1 = fxptSignExtend(lut_odd[idx]);
   end
   FixedPoint#(ri,rf_plus_1) res = out0 + ((out1-out0) * mix);
   return roundLSBs(res);
endfunction: linear_interp

endpackage: SatisfyFV
