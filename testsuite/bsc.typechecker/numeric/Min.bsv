// Test that Min is available as a typeclass

function Bit#(m) fn (Bit#(x) v1, Bit#(y) v2)
 provisos( Min#(x,y,m) );
   return ?;
endfunction

