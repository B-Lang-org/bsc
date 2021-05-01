typedef struct {
   Bool first;
   Bool second;
} OneTwo deriving (Bits);

function Bool foo(OneTwo y);
  Bool x;
  x = True;
  case (y) matches
    OneTwo { first: True } : x = False;
    OneTwo { second: .v } : x = !v;
  endcase
  foo = x;
endfunction: foo

