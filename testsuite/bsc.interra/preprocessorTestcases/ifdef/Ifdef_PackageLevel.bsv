/*
PURPOSE - Simple testcase using the 'define preprocessor directive
 
*/
package Design ;

import Vector::*;

`define max 23

`ifdef MAX
function Bit#(4) result (Bit #(4) x);
Bit #(4) res;
  res = x ^ (x >> 1) ;
  return res;
endfunction 
`else
 
function Bit#(4) result (Bit #(4) x);
Bit #(4) res;
  res = x ^ (x >> 2) ;
  return res;
endfunction 
`endif


endpackage