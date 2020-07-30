function Bool fn (Bit#(x) v1, Bit#(y) v2, Bit#(z) v3);
   Bit#(TAdd#(y,z)) n1 = {v2, v3};
   Bit#(TAdd#(z,TAdd#(y,x))) n2 = {v3, {v2, v1}};
   return ({v1, n1} == n2);
endfunction
