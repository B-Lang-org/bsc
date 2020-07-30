typedef union tagged {
   struct {
      Bool first;
      Bool second;
   } OneTwo;
   void Three;
} TaggedUnionStruct;

function Bool foo(TaggedUnionStruct obj);
  Bool ans1, ans2;
  case (obj) matches
    tagged OneTwo { first: True, second: True }: ans1 = True;
    tagged OneTwo { first: True, second: .second }: ans1 = True;
    tagged OneTwo { first: .first, second: .second }: ans1 = False;
    tagged Three: ans1 = False;
  endcase
  case (obj) matches
    tagged OneTwo { first: .first, second:.second }: ans2 = !first;
    tagged Three: ans2 = False;
  endcase
  foo = ans1 && ans2;
endfunction: foo
