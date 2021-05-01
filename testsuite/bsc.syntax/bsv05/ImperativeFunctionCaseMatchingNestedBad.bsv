typedef union tagged {
   struct {
      Bool first;
      Bool second;
   } OneTwo;
   void Three;
} TaggedUnionStruct;

function Bool foo(TaggedUnionStruct obj);
  Bool ans;
  case (obj) matches
    // Accidentally use '=' for the struct fields
    tagged OneTwo { first = .first, second = .second }: ans = !first;
    tagged Three: ans = False;
  endcase
  foo = ans;
endfunction: foo
