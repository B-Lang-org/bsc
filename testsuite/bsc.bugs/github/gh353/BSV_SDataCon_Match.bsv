import Types::*;

// The existence of a struct is visible:

function t myHead (MyList2 #(t) ts);
  case (ts) matches
    tagged Cons .x : return x.head;
    tagged Nil : return ?;
  endcase
endfunction

// The existence of a struct is no longer visible:

function t head (MyList1 #(t) ts);
  case (ts) matches
    tagged Cons .x : return x._1;
    tagged Nil : return ?;
  endcase
endfunction

// Which also means that you can't write this:

function bool isSingleton (MyList1 #(t) ts);
  case (ts) matches
    tagged Cons .* : return False;
    tagged Nil : return True;
  endcase
endfunction
