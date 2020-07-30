
// Add a sign bit to an unsigned value
function Int#(n) add_sign(UInt#(m) x)
   provisos(Add#(m,1,n));  // n = m + 1
   return unpack({1'b0,pack(x)});
endfunction: add_sign

interface PipeFragment#(type in, type out);
   method ActionValue#(Maybe#(out)) exec(Maybe#(in) x);
endinterface

module mkDivide(PipeFragment#(Tuple2#(FixedPoint#(ni,nf),
				      FixedPoint#(di,df)),
			      FixedPoint#(qi,qf)))
   provisos(Add#(di,df,d_sz), Add#(ni,nf,n_sz), Add#(qi,qf,q_sz),
	    Add#(8,_nat1,d_sz),        // d_sz >= 8
	    Add#(9,_nat1,d_sz_plus_1), // d_sz + 1 >= 9
            Add#(d_sz_minus_1,1,d_sz), Add#(d_sz_minus_2,2,d_sz),
	    Add#(1,d_sz,d_sz_plus_1), Add#(5,d_sz,d_sz_plus_5), Add#(9,d_sz,d_sz_plus_9),
            Add#(2,d_sz_minus_1,d_sz_plus_1),  // d_sz - 1 + 2 == d_sz + 1
	    Add#(4,d_sz_plus_5,d_sz_plus_9),   // d_sz + 5 + 4 == d_sz + 9
	    Add#(6,d_sz_minus_1,d_sz_plus_5),  // d_sz - 1 + 6 == d_sz + 5
	    Add#(1,d_sz_minus_2,d_sz_minus_1), // d_sz - 2 + 1 == d_sz - 1
	    Bits#(FixedPoint#(2,d_sz_minus_2), d_sz),
	    Log#(d_sz_minus_2,sh_bits),
            Arith#(FixedPoint#(4,d_sz_plus_5)),
	    Add#(3,ni,ni_plus_3), Add#(10,nf,nf_plus_10),
            Add#(13,n_sz,n_sz_plus_13),
            Add#(ni_plus_3,nf_plus_10,n_sz_plus_13),
	    Bitwise#(FixedPoint#(ni_plus_3, nf_plus_10)),
	    Bits#(FixedPoint#(1,d_sz_minus_1), d_sz)
	   );
   
   Reg#(Maybe#(Tuple3#(FixedPoint#(ni,nf),
		       FixedPoint#(1,d_sz_minus_1),
		       UInt#(sh_bits)))) buf_d1 <- mkReg(tagged Invalid);

   Reg#(Maybe#(Tuple4#(FixedPoint#(ni,nf),
		       FixedPoint#(3,6),
		       FixedPoint#(1,14),
		       UInt#(sh_bits)))) buf_d2 <- mkReg(tagged Invalid);

   Reg#(Maybe#(Tuple3#(FixedPoint#(ni,nf),
		       FixedPoint#(3,10),
		       UInt#(sh_bits)))) buf_d3 <- mkReg(tagged Invalid);
   
   Reg#(Maybe#(FixedPoint#(qi,qf))) buf_d4 <- mkReg(tagged Invalid);
   
   method ActionValue#(Maybe#(FixedPoint#(qi,qf)))
          exec(Maybe#(Tuple2#(FixedPoint#(ni,nf), FixedPoint#(di,df))) args);

      // Stage 1
      case (args) matches
	 tagged Invalid: buf_d1 <= tagged Invalid;
	 tagged Valid {.n, .d}:
	    begin
	       Bit#(d_sz) bs = pack(d);
	       FixedPoint#(2,d_sz_minus_2) tmp = unpack(bs);
               match {.d_normalized, .shift} = normalize(tmp);
	       FixedPoint#(1,d_sz_minus_1) y_normalized = movePoint(d_normalized);
	       buf_d1 <= tagged Valid tuple3(n, y_normalized, shift);
	    end
      endcase
      
      // Stage 2
      case (buf_d1) matches
	 tagged Invalid: buf_d2 <= tagged Invalid;
	 tagged Valid {.x, .y_normalized, .shift}:
	    begin
	       FixedPoint#(2,d_sz_minus_1) zext_y_normalized = zextMSBs(y_normalized);
	       FixedPoint#(2,7) lut_in1 = roundLSBs(zext_y_normalized);
	       FixedPoint#(3,6) lut_out = recip_small(lut_in1);
	       FixedPoint#(4,d_sz_plus_5) product = fxptMult(y_normalized,lut_out);
	       FixedPoint#(1,14) err = adjust(1 - product);
	       buf_d2 <= tagged Valid tuple4(x, lut_out, err, shift);
	    end
      endcase
      
      // Stage 3
      case (buf_d2) matches
	 tagged Invalid: buf_d3 <= tagged Invalid;
	 tagged Valid {.x, .lut_out, .err, .shift}:
	    begin
	       FixedPoint#(1,14) correction = dropMSBs(roundLSBs(fxptMult(lut_out,err)));
	       FixedPoint#(3,14) f1 = sextMSBs(padLSBs(lut_out));
	       FixedPoint#(3,14) f2 = sextMSBs(correction);
	       FixedPoint#(3,10) newton = dropMSBs(dropLSBs(f1 + f2));
	       buf_d3 <= tagged Valid tuple3(x, newton, shift);
	    end
      endcase
      
      // Stage 4
      case (buf_d3) matches
	 tagged Invalid: buf_d4 <= tagged Invalid;
	 tagged Valid {.x, .y_newton, .shift}:
	    begin
	       let s = fromInteger(valueOf(di) - 1) - add_sign(shift);
	       let z0 = fxptMult(x,y_newton);
	       FixedPoint#(14,24) z = adjust((s < 0) ? (z0 << -s) : (z0 >> s));
	       buf_d4 <= tagged Valid adjust(z);
	    end
      endcase
      
      // Return value
      return buf_d4;
      
   endmethod
endmodule: mkDivide


// -------------------------

// Move the fixed point of a value without changing the
// total number of bits.  This is like a shift that does not lose
// any precision, and it is purely a type-level operation with
// no hardware cost.
function FixedPoint#(ri,rf) movePoint(FixedPoint#(i,f) a)
   provisos(Add#(ri,rf,sz), Add#(i,f,sz));
   return _fromInternal(_toInternal(a));
endfunction: movePoint

// Add zeros to the LSB of a fixed point value
function FixedPoint#(i,rf) padLSBs(FixedPoint#(i,f) a)
   provisos(Add#(d,f,rf), Add#(i,f,in_sz), Add#(i,rf,out_sz), Add#(d,in_sz,out_sz));
   Bit#(d) zeros = '0;
   return unpack({pack(a), zeros});
endfunction: padLSBs

// Reduce the fractional bits of a fixed point value, discarding
// the low bits without rounding.
function FixedPoint#(i,rf) dropLSBs(FixedPoint#(i,f) a)
   provisos(Add#(_1,rf,f), Add#(i,f,a_sz), Add#(i,rf,r_sz));
   Bit#(a_sz) bits = pack(_toInternal(a));
   Int#(r_sz) out = unpack(bits[valueOf(a_sz)-1 : valueOf(a_sz)-valueOf(r_sz)]);
   return _fromInternal(out);
endfunction: dropLSBs

// Reduce the fractional bits of a fixed point value with rounding.
// Positive values round up if the fractional part is >= 0.5.
// Negative values round toward negative infinity if the fractional 
// part is > 0.5.
// NOTE: The provisos for this do not check that rf < f, only that
// rf <= f.  This can allow an index out of range error, but adding
// that check into the provisos causes troublesome constraints to
// propagate out to callers of this function.
function FixedPoint#(i,rf) roundLSBs(FixedPoint#(i,f) a)
   provisos(Add#(i,f,a_sz), Add#(i,rf,r_sz), Add#(_,r_sz,a_sz));
   let n = _toInternal(a);
   let s = valueOf(a_sz) - valueOf(r_sz);
   Int#(r_sz) v = truncate(n >> s);
   Bool add_one = (pack(n)[s-1] == 1);
   return _fromInternal(add_one ? (v+1) : v);
endfunction: roundLSBs

// Sign extend the MSBs
function FixedPoint#(ri,f) sextMSBs(FixedPoint#(i,f) a)
   provisos(Add#(i,f,a_sz), Add#(ri,f,r_sz), Add#(_,a_sz,r_sz));
   return _fromInternal(signExtend(_toInternal(a)));
endfunction: sextMSBs

// Zero extend the MSBs
function FixedPoint#(ri,f) zextMSBs(FixedPoint#(i,f) a)
   provisos(Add#(i,f,a_sz), Add#(ri,f,r_sz), Add#(_,a_sz,r_sz));
   return _fromInternal(zeroExtend(_toInternal(a)));
endfunction: zextMSBs

// Reduce the integer size of a fixed point value, truncating
function FixedPoint#(ri,f) dropMSBs(FixedPoint#(i,f) a)
   provisos(Add#(i,f,in_sz), Add#(ri,f,out_sz), Add#(_,out_sz,in_sz));
   return _fromInternal(truncate(_toInternal(a)));
endfunction: dropMSBs

// Adjust both ends of a fixed point value
function FixedPoint#(ri,rf) adjust(FixedPoint#(ai,af) a)
   provisos(Add#(ai,af,a_sz), Add#(ri,rf,r_sz), Add#(ai,ri,ki), Add#(af,rf,kf));
   let base = pack(_toInternal(a));
   Bit#(ai) int_part = base[valueOf(a_sz)-1 : valueOf(af)];
   Bit#(af) frac_part = base[valueOf(af)-1 : 0];
   Bit#(ki) int_out = signExtend(int_part);
   Bit#(kf) frac_out = {frac_part, '0};
   Bit#(ri) i = int_out[valueOf(ri)-1 : 0];
   Bit#(rf) f = frac_out[valueOf(kf)-1 : valueOf(kf) - valueOf(rf)];
   Int#(r_sz) res = unpack({i,f});
   return _fromInternal(res);
endfunction: adjust

function Tuple2#(Bit#(n),Bit#(m)) shift_up(Bit#(n) bits, Bit#(m) mask, Integer amt);
   let bits2 = bits;
   let mask2 = mask;
   Bit#(n) check = '1 ^ fromInteger((2**(valueOf(n)-amt)) - 1);
   if ((bits & check) == 0)
      begin
	 bits2 = bits << amt;
	 mask2 = mask | fromInteger(amt);
      end
   if (amt > 1)
      begin
	 match {.bs, .m} = shift_up(bits2, mask2, amt/2);
	 bits2 = bs;
	 mask2 = m;
      end
   return tuple2(bits2,mask2);
endfunction: shift_up

// Shift value left so that 1 <= result < 2, unless it is already greater
// than 2.
function Tuple2#(FixedPoint#(i,f),UInt#(logf)) normalize(FixedPoint#(i,f) x)
   provisos(Add#(i,f,n), Log#(f,logf), Add#(1,f,f_plus_1), Add#(_,f_plus_1,n));
   let bits = pack(_toInternal(x));
   let msb = valueOf(n)-1;
   Bit#(i) int_bits = bits[valueOf(n)-1:valueOf(f)];
   Bit#(f) frac_bits = bits[valueOf(f)-1:0];
   if (int_bits != 0)
      return tuple2(x,0);
   else
      begin
	 Bit#(logf) zero = 0;
         match {.res,.sh} = shift_up({1'b0,frac_bits}, zero, 2**(valueOf(logf)-1));
	 return tuple2(_fromInternal(unpack({'0,res})),unpack(sh));
      end
endfunction: normalize

// -------------------------

// 1/x for 0.5 <= x <= 1.  Results are in the range 1 to 2
(* noinline *)
function FixedPoint#(3,6) recip_small(FixedPoint#(2,7) x);
   // XXX Not important for this example
   return ?;
endfunction: recip_small

// ----------------------------------------------------------------------

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

instance Literal#( FixedPoint#(i,f) )
   provisos( Add#(i,f,b) );

   // A way to convert Integer constants to fixed points
   function FixedPoint#(i,f) fromInteger( Integer n) ;

      // Convert to explicit types to all for bounds checking
      Int#(i) conv = fromInteger(n) ;
      return FixedPoint {i:pack(conv),
                         f:0 };
   endfunction
   function inLiteralRange(f,n);
      Int#(i) int_part = ?;
      return(inLiteralRange(int_part,n));
   endfunction
endinstance

instance Arith#( FixedPoint#(i,f) )
   provisos( Add#(i,f,b)
            ,Add#(TAdd#(i,i), TAdd#(f,f), TAdd#(b,b))
            );

   // Addition does not change the binary point
   function FixedPoint#(i,f) \+ (FixedPoint#(i,f) in1, FixedPoint#(i,f) in2 );
       return _fromInternal ( _toInternal (in1) + _toInternal (in2) ) ;
   endfunction

   // Similar subtraction does not as well
   function FixedPoint#(i,f) \- (FixedPoint#(i,f) in1, FixedPoint#(i,f) in2 );
       return _fromInternal ( _toInternal (in1) - _toInternal (in2) ) ;
   endfunction

   // negate is defined in terms of the subtraction operator.
   function FixedPoint#(i,f) negate (FixedPoint#(i,f) in1 );
      return _fromInternal ( 0 - _toInternal(in1) );
   endfunction

   // The rest are not needed for this design

   function FixedPoint#(i,f) \* (FixedPoint#(i,f) in1, FixedPoint#(i,f) in2 );
      return error ("The operator " + quote("*") +
                    " is not defined for " + quote("FixedPoint") + ".");
   endfunction

   function FixedPoint#(i,f) \/ (FixedPoint#(i,f) in1, FixedPoint#(i,f) in2);
      return error ("The operator " + quote("/") +
                    " is not defined for " + quote("FixedPoint") + ".");
   endfunction

   function FixedPoint#(i,f) \% (FixedPoint#(i,f) in1, FixedPoint#(i,f) in2);
      return error ("The operator " + quote("%") +
                    " is not defined for " + quote("FixedPoint") + ".");
   endfunction

   function FixedPoint#(i,f) abs( FixedPoint#(i,f) x);
      return error ("The function " + quote("abs") +
                    " is not defined for " + quote("FixedPoint") + ".");
   endfunction

   function FixedPoint#(i,f) signum( FixedPoint#(i,f) x);
      return error ("The function " + quote("signum") +
                    " is not defined for " + quote("FixedPoint") + ".");
   endfunction

   function \** (x,y);
      return error ("The operator " + quote("**") +
                    " is not defined for " + quote("FixedPoint") + ".");
   endfunction

   function exp_e(x);
      return error ("The function " + quote("exp_e") +
                    " is not defined for " + quote("FixedPoint") + ".");
   endfunction

   function log(x);
      return error ("The function " + quote("log") +
                    " is not defined for " + quote("FixedPoint") + ".");
   endfunction

   function logb(b,x);
      return error ("The function " + quote("logb") +
                    " is not defined for " + quote("FixedPoint") + ".");
   endfunction

   function log2(x);
      return error ("The function " + quote("log2") +
                    " is not defined for " + quote("FixedPoint") + ".");
   endfunction

   function log10(x);
      return error ("The function " + quote("log10") +
                    " is not defined for " + quote("FixedPoint") + ".");
   endfunction

endinstance

function FixedPoint#(ri,rf)  fxptMult( FixedPoint#(ai,af) a,
                                       FixedPoint#(bi,bf) b  )
   provisos (Add#(ai,bi,ri)   // ri = ai + bi
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

// ----------------------------------------------------------------------

