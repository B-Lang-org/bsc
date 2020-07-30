package Design ;

import Vector::*;



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
`define MAX 23
`undef MAX
 method Bit#(4) out_data(Bit#(4) in_data);
`ifdef MAX
    out_data = 11; 
`else
    out_data = 12;
`endif
  endmethod: out_data

endmodule : mkDesign
endpackage: Design 
