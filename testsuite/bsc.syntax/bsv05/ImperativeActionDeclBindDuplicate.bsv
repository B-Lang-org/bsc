function Action f();
  action
    bit[3:0] x;
    x <- actionvalue return(3); endactionvalue;
    x <- actionvalue return(42); endactionvalue;
  endaction
endfunction
