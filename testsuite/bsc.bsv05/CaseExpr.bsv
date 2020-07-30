function int f(Bool y);
  f = case (y)
        True: return 5;
        False: return 7;
      endcase;
endfunction: f
