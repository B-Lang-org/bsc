package ActionValueImports;

// Test all arguments in each function, but mix the order up a little

// narrow result
import "BDPI"
    function ActionValue#(Bit#(32))
        av_narrow (Bit#(128) w, Bit#(sz) p, Bit#(32) n, String s);

// wide result
import "BDPI"
    function ActionValue#(Bit#(128))
        av_wide (String s, Bit#(32) n, Bit#(sz) p, Bit#(128) w);

// poly result
import "BDPI"
    function ActionValue#(Bit#(sz))
        av_poly (Bit#(sz) p, String s, Bit#(128) w, Bit#(32) n);

// Test no BSV arguments

// narrow result
import "BDPI" function ActionValue#(Bit#(32)) random_narrow();

// wide result
import "BDPI" function ActionValue#(Bit#(128)) random_wide();

// Action used to reset random seed for predictability
// Note: this is importing a function directly from
// the C standard library!
import "BDPI" function Action srandom(Bit#(32) seed);

endpackage
