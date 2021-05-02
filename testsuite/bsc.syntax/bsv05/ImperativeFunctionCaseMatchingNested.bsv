typedef union tagged {
   struct {
      Bool first;
      Bool second;
   } OneTwo;
   void Three;
   Tuple2#(Bool,Bool) Four;
} TaggedUnionStruct;

function Bool foo(TaggedUnionStruct obj);
  Bool ans1, ans2, ans3;
  case (obj) matches
    tagged OneTwo { first: True, second: True }: ans1 = True;
    tagged OneTwo { first: True, second: .second }: ans1 = True;
    tagged OneTwo { first: .first, second: .second }: ans1 = False;
    tagged Three: ans1 = False;
    tagged Four { True, .* }: ans1 = True;
    tagged Four { .a, .b }: ans1 = a && b;
  endcase
  case (obj) matches
    tagged OneTwo { first: .first, second:.second }: ans2 = !first;
    tagged Three: ans2 = False;
    tagged Four .*: ans2 = True;
  endcase
  // Test without field names
  case (obj) matches
    tagged OneTwo { }: ans3 = True;
    tagged Three: ans3 = False;
    tagged Four { True, True }: ans3 = True;
    tagged Four { .*, .* }: ans3 = False;
  endcase
  foo = ans1 && ans2 && ans3;
endfunction: foo
