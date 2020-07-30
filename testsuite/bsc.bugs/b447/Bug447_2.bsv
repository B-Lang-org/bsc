package Temp_Uninitialised;

interface Temp_Uninitialised_IFC;

method Action set_in (Bit#(1) a, Bit#(1) b);

method Bit#(1) out; 

endinterface: Temp_Uninitialised_IFC

(*
    always_enabled,
    always_ready,
    CLK = "clk",
    RST_N = "reset"
*)

module mkTemp_Uninitialised(Temp_Uninitialised_IFC);

Reg#(Bit#(1)) reg_a();
mkRegA#(0) reg_a_inst(reg_a);

method set_in (a,b);

action

  Bit#(1) wireID;
       
    reg_a <= a & b;

    wireID <= reg_a;

endaction

endmethod

method out;

out = reg_a;

endmethod

endmodule: mkTemp_Uninitialised

endpackage: Temp_Uninitialised
