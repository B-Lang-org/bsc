// ----------------------------------------------------------------
// This function adds two arguments of width n1 and produces a
// result of width n2 = n1+1, so that no bits are lost

function t1#(n2) wideningPlus (t1#(n1) x, t1#(n1) y)
         provisos (BitExtend#(n1, n2, t1),
                   Add#(n1, 1, n2),
                   Arith#(t1#(n2))
                   );
   t1#(n2) xx = extend (x);
   t1#(n2) yy = extend (y);
   return (xx + yy);
endfunction

