function Action f(Bool cond, Reg#(bit [3:0]) r);
  action
    if (cond)
      (action r <= 3; endaction);
    else
      (action r <= 5; endaction);
  endaction
endfunction
