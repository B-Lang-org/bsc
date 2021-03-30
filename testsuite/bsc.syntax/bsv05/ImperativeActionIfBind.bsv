function Action f(Bool cond);
  action
    bit[3:0] x;
    if (cond)
      x <- actionvalue return(3); endactionvalue;
    else
      x <- actionvalue return(5); endactionvalue;
  endaction
endfunction
