function Bool f(Maybe#(Bool) m);
  Bool res;
  if (m matches tagged Valid .m) res = True; else res = False;
  f = res;
endfunction
