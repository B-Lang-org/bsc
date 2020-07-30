function Bool fn1(Maybe#(String) m);
   case (m) matches
      tagged Valid "foo" : return True;
      default : return False;
   endcase
endfunction

function Bool fn2(Maybe#(Char) m);
   case (m) matches
      tagged Valid "a" : return True;
      default : return False;
   endcase
endfunction

