// Test that the leading minus in Integer and Real literals is applied to
// literal before fromInteger or fromReal.  This is tested by using a type
// for which Arith (and thus "negate") is not defined.  If the minus sign
// were left as an application of "negate", then BSC would give a proviso
// error.

typedef struct { Integer x; Real y; Bit#(n) z; } S#(type n);

instance Literal#(S#(sz));
   function S#(sz) fromInteger(Integer n);
      return (S {x: n, y: 0, z: 0});
   endfunction
   function Bool inLiteralRange(S#(sz) s, Integer n);
      return True;
   endfunction
endinstance

instance RealLiteral#(S#(sz));
   function S#(sz) fromReal(Real n);
      return (S {x: 0, y: n, z: 0});
   endfunction
endinstance

instance SizedLiteral#(S#(sz), sz);
   function S#(sz) fromSizedInteger(Bit#(sz) n);
      return (S {x: 0, y: 0, z: n});
   endfunction
endinstance


// Create from literals
S#(4) neg_one           = -1;
S#(4) neg_one_point_one = -1.1;
S#(4) neg_one_size4     = -4'd1;
