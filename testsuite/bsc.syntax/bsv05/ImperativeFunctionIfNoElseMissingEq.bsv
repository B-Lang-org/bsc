function bit[3:0] f(Bool cond);
  bit[3:0] x;
  if (cond)
    x = 3;
  f = x;
endfunction
