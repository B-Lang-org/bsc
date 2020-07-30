function bit[3:0] f(Maybe#(Bool) cond);
  bit[3:0] x;
  if (cond matches Invalid)
    x = 3;
  else
    x = 5;
  f = x;
endfunction
