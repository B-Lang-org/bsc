function bit[3:0] f(Bool cond);
  bit[3:0] x;
  if (cond)
    x = 3;
  else
    x = 5;
  f = x;
endfunction
