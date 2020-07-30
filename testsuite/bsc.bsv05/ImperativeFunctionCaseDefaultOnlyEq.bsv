function bit[3:0] f(Bool test, Bool cond1, Bool cond2);
  bit[3:0] x;
  bit[3:0] y;
  case (test)
    default: x = 5;
  endcase
  f = x;
endfunction
