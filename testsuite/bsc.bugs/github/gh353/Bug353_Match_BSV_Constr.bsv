
import Bug353_Type::*;


typedef struct {
  Bool f1;
  Bool f2;
} Foo deriving (Bits);


// -----

module mkMod (Bool);
  match tagged Foo { f1: .x, f2: .y } = ?;
  return (x && y);
endmodule
