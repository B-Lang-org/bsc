package ValueImports;

// String arguments
import "BDPI" function Bool string_compare (String s1, String s2);

// Narrow vector arguments and result
import "BDPI" function Bit#(32) and32 (Bit#(32) v1, Bit#(32) v2);

// Wide vector arguments and result
import "BDPI" function Bit#(128) and128 (Bit#(128) v1, Bit#(128) v2);

// Poly vector arguments and result
import "BDPI" andN =
    function Bit#(n) andN_prim (Bit#(n) v1, Bit#(n) v2, Bit#(32) sz);

function Bit#(n) andN (Bit#(n) v1, Bit#(n) v2);
    return andN_prim(v1, v2, fromInteger(valueOf(n)));
endfunction

// Test no arguments
import "BDPI" function Bit#(32) const_narrow ();

import "BDPI" function Bit#(128) const_wide ();

endpackage

