function bit[3:0] f();
  bit[3:0] x;
  x = 3;
  x = x;
  f = x;
endfunction
