function Action f(Bool cond, Reg#(bit [3:0]) r);
  action
    if (cond)
      r <= 3;
    else
      r <= 5;
  endaction
endfunction
