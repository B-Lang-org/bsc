function Bit#(nm) fn(Bit#(n) v1, Bit#(m) v2)
   provisos(NumAlias#(TAdd#(n), nm));

   return {v1, v2};
endfunction
