function Bool f(Maybe#(Bool) m);
  Bool res;
  case (m) matches
    tagged Invalid: res = True;
    tagged Valid (.m): res = False;
  endcase
  f = res;
endfunction
