typedef enum { X, Y, Z} L deriving(Eq);

(* noinline *)
function Bool fnNoInline_ArgNotInBits (L x);
   return (x == Y);
endfunction

