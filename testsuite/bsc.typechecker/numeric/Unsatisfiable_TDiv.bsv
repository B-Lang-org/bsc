// TDiv requires that the second type not be 0
// but the Add proviso is only satisfiable if that type is 0
//
function Bool fn1(Bit#(n) x, Bit#(m) y)
 provisos (Add#(m, n, m), Div#(m, n, k));
   return ?;
endfunction

