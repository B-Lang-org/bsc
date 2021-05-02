function Bool foo(Tuple2#(Bool,Maybe#(Bool)) v);
  Bool res;
  case (v) matches
    { True, tagged Valid True }: res = True;
    { False, tagged Valid .b }: res = b;
    { .*, .* }: res = False;
  endcase
  foo = res;
endfunction: foo
