
package Design ;

import Vector::*;

`define 1222 12

interface Design_IFC ;
    method Bit#(4) out_data(Bit#(4) in_data);
endinterface: Design_IFC

function Bit#(4) result (Bit #(4) x);
Bit #(4) res;
  res = x ^ (x >> 1) ;
  return res;
endfunction 

(*
       always_ready ,
       always_enabled ,
       clock_prefix = "clk",
       reset_prefix = "reset"
*)

module mkDesign (Design_IFC);


 method Bit#(4) out_data(Bit#(4) in_data);
`define MAX 23
    if(`MAX > 12) 
      out_data = 12;
    else 
      out_data = 13;
  endmethod: out_data

endmodule : mkDesign
endpackage: Design 
