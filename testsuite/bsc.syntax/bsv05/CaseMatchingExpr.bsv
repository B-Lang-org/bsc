function int f(Maybe#(Bool) m);
  f = case (m) matches
        tagged Invalid: return 5;
        tagged Valid (True): return 7;
        tagged Valid (False): return 15;
      endcase;
endfunction: f
