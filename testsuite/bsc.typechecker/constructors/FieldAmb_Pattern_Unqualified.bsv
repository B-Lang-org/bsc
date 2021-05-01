import FieldAmb_Pattern_Sub::*;

typedef struct {
   t f;
} S#(type t);

function t getF(S#(t) sv);
   match S { f : .fv } = sv;
   return fv;
endfunction

