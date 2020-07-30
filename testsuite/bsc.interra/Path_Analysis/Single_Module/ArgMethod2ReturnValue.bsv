// Create a simple among local definition variables.
// A cycle should be detected prior to scheduling
// Should report an error with -verilog flag!
// Cycle from argument of a method to its return value
// Cycle created in a method

package ArgMethod2ReturnValue;

interface ArithIO ;
    method Action setInput();
endinterface: ArithIO

(* synthesize *)
module [Module] mkArgMethod2ReturnValue(ArithIO);

    RWire#(Bit #(2)) x();
    mkRWire the_x(x);

    Bit #(2) temp1 = x.wget matches tagged Just {.x} ? x: 0;
    Bit #(2) temp2 = (temp1 == 0) ? 3: 1;
    temp2 = temp2 + temp1;
    Action temp3 = x.wset (temp2);
 
    method Action setInput();
         temp3;
    endmethod: setInput

endmodule

endpackage 

