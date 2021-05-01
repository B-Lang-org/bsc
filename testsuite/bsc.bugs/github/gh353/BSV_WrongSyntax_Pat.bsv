typedef struct {
  Bool f1;
  Bool f2;
} S;

typedef union tagged {
  struct { Bool f1; Bool f2; } C;
} U;

// -----
// Try using struct syntax for a constructor

function Bool fn1 (U v);
  case (v) matches
    C { f1: .x, f2: .y }: return (x && y);
    default: return False;
  endcase
endfunction

// -----
// Try using constructor syntax for a struct

function Bool fn2 (S v);
  case (v) matches
    tagged S { f1: .x, f2: .y }: return (x && y);
    default: return False;
  endcase
endfunction
