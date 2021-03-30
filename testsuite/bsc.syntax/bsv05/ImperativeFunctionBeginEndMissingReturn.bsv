function int f();
  int x = 1;
  int y = case (x)
  1: begin x; end
  default: x;
  endcase;
  y;
endfunction
