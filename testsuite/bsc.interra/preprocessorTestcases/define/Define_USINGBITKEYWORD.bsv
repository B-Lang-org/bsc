/*
PURPOSE - Simple testcase using the 'define preprocessor directive
 
*/
package Design ;

import Vector::*;
`define Bit 11



function Bit#(4) result (Bit #(4) x);
Bit #(4) res;
  res = x ^ (x >> 1) ;
  return res;
endfunction 

endpackage
