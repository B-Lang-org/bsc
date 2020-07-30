/*
PURPOSE - Simple testcase using the 'define preprocessor directive
 
*/
package Design ;

import Vector::*;

`define max true

function Bit#(4) result (Bit #(4) x);
 if(max)
    return 10;
 else
    return 11;
endfunction 

endpackage