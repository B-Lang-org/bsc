package Design ;

import Vector::*;

`define MAX 23

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
//`ifdef MAX

  method Bit#(4) out_data(Bit#(4) in_data);
      out_data = 12; 
  endmethod: out_data
//`else 
 method Bit#(4) out_data(Bit#(4) in_data);
      out_data = result(in_data + 1 );
 endmethod: out_data
`endif

endmodule : mkDesign
endpackage: Design 
