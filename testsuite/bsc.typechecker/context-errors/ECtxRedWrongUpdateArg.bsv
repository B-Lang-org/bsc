//Parser bug prevents this code from working
//Bool x[2] = {True, True};
//Bit#(1) y = x[0];

function Bool f();
   Bool x[2] = {True, True};
   Bit#(1) y = 1;
   x[0] = y;
   return x[0];
endfunction

