package Design ;

import Vector::*;



interface Design_IFC ;
    method Bit#(4) out_data(Bit#(4) in_data);
endinterface: Design_IFC
`define MAX 23

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
    Bit#(4) temp = 10;
     if(temp > `MAX)
        out_data = result(in_data);
     else
      out_data = result(in_data+1);        
  endmethod: out_data

endmodule : mkDesign
endpackage: Design 
