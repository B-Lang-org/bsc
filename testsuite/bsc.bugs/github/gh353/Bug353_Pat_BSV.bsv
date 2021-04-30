
import Bug353_Type::*;


typedef struct {
  Bool f1;
  Bool f2;
} Foo deriving (Bits);


// -----
// Trigger error T0020

function Bool fn1 (Foo v);
  case (v) matches
    tagged Foo { f1: .x, f2: .y }: return (x && y);
    default: return False;
  endcase
endfunction
