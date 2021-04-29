typedef struct {
  Bool f1;
  Bool f2;
} S;

typedef union tagged {
  struct { Bool f1; Bool f2; } C;
} U;

// -----
// Try using struct syntax for a constructor

function U fn1 ();
  return C { f1: True, f2: False };
endfunction

// -----
// Try using constructor syntax for a struct

function S fn2 ();
  return tagged S { f1: True, f2: False };
endfunction
