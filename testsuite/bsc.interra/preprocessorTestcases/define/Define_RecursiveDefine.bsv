/*
PURPOSE - Simple testcase using the 'define preprocessor directive
 
*/
package Design ;

import Vector::*;

`define max_val max_val + 1
`define bus_width top.bus_width

function Bit#(4) result (Bit #(4) x);
  if(`max_val > 1 ) 
    return 10;
 else
    return 11;
endfunction 

endpackage

