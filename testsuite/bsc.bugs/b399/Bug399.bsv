package Bug399;


interface DESIGN_IFC;
   method Bit#(8) out_data(Bit#(8) in_data,Bit#(1) shift_dir,Bit#(1) circular);
endinterface: DESIGN_IFC


function Bit#(8) result (Bit#(8) in_data,Bit#(1) shift_dir,Bit#(1) circular);
Bit#(8) res;
       case ({shift_dir,circular})
             2'b00: res = in_data << 1;
             2'b01: res = {in_data[6:0],in_data[7:7]};
             2'b10: res =  in_data >> 1;
             2'b11: res = {in_data[0:0],in_data[7:1]};
             default : res = ?;
       endcase
   return res;
endfunction


(* 
       synthesize ,
       always_ready ,
       always_enabled ,
       no_default_clock ,
       no_default_reset
 *)

module mkBug399 (DESIGN_IFC);

  method Bit#(8) out_data(Bit#(8) in_data, Bit#(1) shift_dir, Bit#(1) circular);
    out_data = result(in_data,shift_dir,circular);
  endmethod: out_data

endmodule: mkBug399
                 
endpackage: Bug399
