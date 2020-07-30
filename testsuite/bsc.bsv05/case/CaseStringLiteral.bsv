function Bool fn1(String s);
   case (s)
      "foo" : return True;
      default : return False;
   endcase
endfunction

function Bool fn2(Char c);
   case (c)
      "a" : return True;
      default : return False;
   endcase
endfunction

