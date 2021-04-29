
import Types_NonNamed::*;

function Foo fn1 ();
  return tagged Bar { _1: True, _2: False };
endfunction

function Bool fn2 (Foo v);
  case (v) matches
    tagged Bar { _1: .x, _2: .y }: return (x && y);
    default: return False;
  endcase
endfunction
