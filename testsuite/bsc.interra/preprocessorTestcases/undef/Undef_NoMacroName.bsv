/*
PURPOSE - Simple testcase using the 'define preprocessor directive
 
*/
import Vector::*;




function Bit#(4) result (Bit #(4) x);
Bit #(4) res;
  res = x ^ (x >> 1) ;
  return res;
endfunction 

`undef 