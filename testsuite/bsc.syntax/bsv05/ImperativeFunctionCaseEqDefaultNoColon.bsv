function bit[3:0] f(Bool test, Bool cond1, Bool cond2, Bool cond3);
  bit[3:0] x;
  bit[3:0] y;
  case (test)
    cond1,cond2: x = 3;
    cond3: x = 4;
    default x = 5;
  endcase
  f = x;
endfunction
