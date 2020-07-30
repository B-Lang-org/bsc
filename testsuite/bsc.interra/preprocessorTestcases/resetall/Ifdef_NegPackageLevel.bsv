/*
PURPOSE - Simple testcase using the 'define preprocessor directive
 
*/
package Design ;

import Vector::*;

`define max 23
`resetall

interface Design_IFC ;
    method Bit#(4) out_data(Bit#(4) in_data);
endinterface: Design_IFC



(*
       always_ready ,
       always_enabled ,
       clock_prefix = "clk",
       reset_prefix = "reset"
*)

module mkDesign (Design_IFC);


 method Bit#(4) out_data(Bit#(4) in_data);
`define MAX 23
`undef MAX

`ifdef MAX
    out_data = 12 ;
`else
    out_data = 13;
`endif
  endmethod: out_data

endmodule : mkDesign

endpackage