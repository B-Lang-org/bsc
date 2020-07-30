typedef enum { X, Y, Z} L deriving(Eq);

(* noinline *)
function L fnNoInline_ResNotInBits (Bool x);
   if (x)
      return Y;
   else
      return Z;
endfunction

