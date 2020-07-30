//Parser bug prevents this code from working
//Bool x[2] = {True, True};
//Bit#(1) y = x[0];

function Bit#(1) f();
   Bool x[2] = {True, True};
   Bit#(1) y = x[0];
   return y;
endfunction

