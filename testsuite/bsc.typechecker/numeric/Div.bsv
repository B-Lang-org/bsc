// Test the arithematic rules for Div instances

// ----------------
// A proviso for Div#(x,1,x) should not be needed

function Bit#(z) fnDiv (Bit#(x) v1, Bit#(y) v2) provisos (Div#(x,y,z));
   return 0;
endfunction

// This should not need a proviso
function Bit#(x) test1 (Bit#(x) v1);
   Bit#(1) v2 = 0;
   return (fnDiv(v1,v2));
endfunction

// ----------------

