function bit[3:0] f(Bool cond);
  bit[3:0] x;
  x = 5;
  if (cond)
    x = 3;
  f = x;
endfunction
