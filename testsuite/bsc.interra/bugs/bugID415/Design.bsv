package Design;

interface Design_IFC;

method Bit#(2) out (Bit#(2) get);

endinterface: Design_IFC

(*
   always_enabled,
   always_ready,
   clock_prefix = "clk",
   reset_prefix = "reset"
*)

module mkDesign(Design_IFC);

  method Bit#(2) out (Bit#(2) get);

  Bit#(2) temp;

    temp[0] = get[0];
    temp[1] = get[1];

    out = temp;

  endmethod

endmodule: mkDesign

endpackage: Design
