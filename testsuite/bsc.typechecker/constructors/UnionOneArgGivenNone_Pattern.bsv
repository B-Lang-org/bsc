typedef union tagged { Bool Foo; } Bar;

function Bool findf(Bar x);
   case (x) matches
      //tagged Foo .* : return True;
      tagged Foo : return False;
   endcase
endfunction

