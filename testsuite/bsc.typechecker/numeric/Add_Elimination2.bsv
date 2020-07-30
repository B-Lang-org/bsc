function Bool fn (Bit#(x) v1, Bit#(y) v2, Bit#(z) v3);
   Bit#(TAdd#(y,TAdd#(z,4))) n1 = {v2, {v3, 4'b0}};
   Bit#(TAdd#(TAdd#(1,z),TAdd#(TAdd#(y,1),TAdd#(1,TAdd#(x,1))))) n2 = {{1'b0, v3}, {{v2, 1'b0}, {1'b0, {v1, 1'b0}}}};
   return ({v1, n1} == n2);
endfunction
