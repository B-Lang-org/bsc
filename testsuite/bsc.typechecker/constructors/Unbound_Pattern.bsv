
typedef struct {
   t f;
} S#(type t);

function t getF(S#(t) sv);
   // A typo in the struct name should be reported as unbound
   match D { f : .fv } = sv;
   return fv;
endfunction

