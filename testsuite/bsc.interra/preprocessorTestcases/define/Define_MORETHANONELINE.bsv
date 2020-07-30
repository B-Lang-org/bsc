/*
PURPOSE - Simple testcase using the 'define preprocessor directive
 
*/
package Design ;


`define ONE 111111111111111111111111111111111111111111111111                                 111111111111111



function Bit#(4) result (Bit #(4) x);
Bit #(4) res;
  res = x ^ (x >> 1) ;
  return res;
endfunction 



endpackage