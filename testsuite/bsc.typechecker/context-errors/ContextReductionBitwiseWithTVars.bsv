typedef struct { t fst; t snd; } Pair#(type t);

function Pair#(t) f(Pair#(t) a, Pair#(t) b);
   return (a ^ b);
endfunction

