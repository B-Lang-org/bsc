/*
PURPOSE - Simple testcase using the 'define preprocessor directive
 
*/
package Design ;

`define max 2 


function Bit#(4) result (Bit #(4) x);
  if(`max > 1 ) 
    return 10;
 else
    return 11;
endfunction 

endpackage