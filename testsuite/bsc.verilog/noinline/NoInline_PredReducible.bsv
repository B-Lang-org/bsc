typedef enum { X, Y, Z } L deriving(Eq);

instance Bits#(L,2);
   function pack(x);
      case (x)
	 X: return 0;
	 Y: return 1;
	 Z: return 3;
      endcase
   endfunction
   function unpack(x);
      case (x)
	 0: return X;
	 1: return Y;
	 default: return Z;
      endcase
   endfunction
endinstance

(* noinline *)
function Bit#(m) fn (Bool x) provisos(Bits#(L,m));
   return (x ? 0 : 1);
endfunction

