
typedef union tagged {
  UInt#(k) Fin;
} Fin#(numeric type n, numeric type k) deriving(Eq);

typedef Fin#(n, TLog#(n))  PackedFin#(type n);

// If we know that n = 2^k, there's a unique Bits instance we want
instance Bits#(Fin#(n,k),k)
provisos (Log#(n,k), NumEq#(n, TExp#(TLog#(n))));
  function pack (x);
    if (x matches tagged Fin .i)
      return pack(i);
    else
      return ?;
  endfunction
  function unpack (x);
    return tagged Fin (unpack (x));
  endfunction
endinstance

typedef union tagged {
  PackedFin#(n) IsPackedFin;
  t             IsNotPackedFin;
} PackedFinOr#(type t, numeric type n);

// -----

instance Bits#(PackedFinOr#(t,n), _v100)
provisos (Bits#(PackedFin#(n), _v101),
	  Bits#(t, _v104),
	  Add#(_v102, _v101, _v103),
	  Add#(_v105, _v104, _v103),
	  Max#(_v101, _v104, _v103),
	  Add#(1, _v103, _v100));

  function Bit#(_v100) pack (PackedFinOr#(t,n) x);
    case (x) matches
      tagged IsPackedFin ._x    : return {1'b0, {?, (Bit#(_v101))'(pack(_x))}};
      tagged IsNotPackedFin ._x : return {1'b1, {?, (Bit#(_v104))'(pack(_x))}};
      default : return ?;
    endcase
  endfunction

  function PackedFinOr#(t,n) unpack (Bit#(_v100) x);
    let _y = primSplit (x);
    case ((Bit#(1))'(_y.fst))
      0 : return tagged IsPackedFin unpack(primTrunc(_y.snd));
      1 : return tagged IsNotPackedFin unpack(primTrunc(_y.snd));
      default: return ?;
    endcase
  endfunction
endinstance
