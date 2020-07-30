/*
PURPOSE - Simple testcase using the 'define preprocessor directive
 
*/
package Design ;

import Vector::*;

`define max 1  // This is comment 


function Bit#(4) result (Bit #(4) x);
 if(`max > 1)
    return 10;
 else
    return 11;
endfunction 

endpackage