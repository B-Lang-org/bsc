
function Integer myFn1 (Integer x);
  return (x + 1);
endfunction

(* deprecate="Pragma re-export works" *)
function Integer myFn2 (Integer x);
  return (x - 1);
endfunction

typedef struct {
  Bool b1;
  Bool b2;
} S;

