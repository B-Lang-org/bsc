function bit [3:0] f();
  bit [3:0] x;
  if (True)
    begin
      x = 3;
    end
  else
    begin
      x = 7;
    end
  x = 5;
  f = x;
endfunction
