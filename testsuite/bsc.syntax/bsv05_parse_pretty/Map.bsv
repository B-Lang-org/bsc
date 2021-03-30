import List::*;

function Bool isNull (List#(a) xs);
  case (xs) matches
    tagged Nil: isNull = True;
    default: isNull = False;
  endcase
endfunction

function List#(b) map (function b f(a x), List#(a) xs);
  return (isNull(xs) ? nil : cons(f(head(xs)), map(f,tail(xs))));
endfunction: map
