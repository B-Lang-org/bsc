/*
PURPOSE - Simple testcase using the 'define preprocessor directive
 
*/
package Design ;

import Vector::*;

`define max 23
`define MAX max +3
`define Max MAX + 4
`define MaX Max + 4

function Bit#(4) result (Bit #(4) x);
Bit #(4) res;
  res = x ^ (x >> 1) ;
  return res;
endfunction 

endpackage