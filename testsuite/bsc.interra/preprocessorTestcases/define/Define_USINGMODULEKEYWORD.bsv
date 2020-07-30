/*
PURPOSE - Simple testcase using the 'define preprocessor directive
 
*/
package Design ;

import Vector::*;
`define module 11



function Bit#(4) result (Bit #(4) x);
Bit #(4) res;
  res = x ^ (x >> 1) ;
  return res;
endfunction 

interface Design_IFC ;
    method Bit#(4) out_data(Bit#(4) in_data);
endinterface: Design_IFC

 module mkDesign (Design_IFC);
 method Bit#(4) out_data(Bit#(4) in_data);
      out_data = result(in_data + 1);
  endmethod: out_data
endmodule : mkDesign
endpackage