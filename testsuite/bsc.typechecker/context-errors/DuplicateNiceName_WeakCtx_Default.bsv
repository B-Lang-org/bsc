// Test that if the type already contains compiler-generated names
// (say, the user previously added provisos requested by BSC)
// that the error message recommending more provisos does not
// rename new variables with those same names

// Test it both in the base type (a__) and in a proviso (b__)

// This is missing the proviso Add#(1,_,x) which should use the name c__

function Bit#(z) fn(Bit#(a__) unused, Bit#(x) v)
 provisos (Add#(x, b__, z));

   Bit#(x) v2 = {0, 1'b1};
   return zeroExtend(v & v2);

endfunction