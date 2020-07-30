//Parser bug prevents this code from working
//Bool x[2] = {True, True};
//Bool y = x[True];

function Bool f();
   Bool x[2] = {True, True};
   Bit#(33) idx = 0;
   Bool y = x[idx];
   return y;
endfunction

