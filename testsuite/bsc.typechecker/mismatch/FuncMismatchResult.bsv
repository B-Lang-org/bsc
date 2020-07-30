function Bool f(Bool x, Bool y);
   return x && y;
endfunction

Bit#(1) z = f(True, False);

