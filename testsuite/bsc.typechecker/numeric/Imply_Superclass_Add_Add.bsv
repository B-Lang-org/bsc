typeclass TC#(type n, type k, type m)
 provisos (Add#(n, k, m))
 dependencies ((n, k) determines m, (n, m) determines k, (k,m) determines n);
endtypeclass

// Add#(nn, kk, mm) should not be necessary

function Bit#(TAdd#(m,m)) fn(Bit#(n) v1, Bit#(k) v2)
 provisos (TC#(n, k, m));

   Bit#(TAdd#(n,n)) a = {v1, v1};
   Bit#(TAdd#(k,k)) b = {v2, v2};

   return {a, b};

endfunction

