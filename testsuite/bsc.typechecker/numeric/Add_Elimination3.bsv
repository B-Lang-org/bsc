// Needs Add#(x,y,z)
function Bool fn (Bit#(x) v1, Bit#(y) v2, Bit#(z) v3);
   Bit#(TAdd#(TAdd#(y,2),TAdd#(1,TAdd#(x,1)))) n2 = {{v2, 2'b0}, {1'b0, {v1, 1'b0}}};
   return ({v3, 4'b0} == n2);
endfunction
