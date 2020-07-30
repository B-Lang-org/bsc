function Bool fn(Bit#(n) x)
provisos(Add#(n, j, 3));
   Bit#(TExp#(n)) v1 = 0;
   Bit#(TExp#(j)) v2 = 0;
   Bit#(TExp#(3)) v3 = 0;
   return (v3 == mulFn(v1,v2));
endfunction

function Bit#(n_by_m) mulFn(Bit#(n) x, Bit#(m) y)
provisos(Mul#(n, m, n_by_m));
   return ?;
endfunction