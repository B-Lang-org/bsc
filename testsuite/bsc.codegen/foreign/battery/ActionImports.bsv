package ActionImports;

// Test all arguments in one function!
import "BDPI"
    function Action action_function
        (Bit#(32) n, Bit#(128) w, Bit#(sz) p, String s);

// Test no arguments
import "BDPI" function Action tick ();

endpackage
