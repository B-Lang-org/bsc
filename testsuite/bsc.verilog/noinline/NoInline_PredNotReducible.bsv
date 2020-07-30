typedef enum { X, Y, Z} L deriving(Eq);

// This is not reducible because no Bits instance exists
(* noinline *)
function Bit#(m) fn (Bool x) provisos(Bits#(L,m));
   return (x ? 0 : 1);
endfunction

