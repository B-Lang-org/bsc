package Alternate;

interface Alternate_IFC;

method Action get_in (Bit#(1) in1, Bit#(1) in2, Bit#(1) in3, Bit#(1) in4, Bit#(2) sel);

method Bit#(1) out();

endinterface: Alternate_IFC

(*
   always_enabled,
   always_ready,
   clock_prefix = "clk",
   reset_prefix = "reset"
*)

module mkAlternate(Alternate_IFC);

Reg#(Bit#(1)) reg_out();
mkReg#(0) i_reg_out(reg_out);

  method Action get_in (Bit#(1) in1, Bit#(1) in2, Bit#(1) in3, Bit#(1) in4, Bit#(2) sel);

    action

    if (sel[0] == 1'b0)
        reg_out <= in1;

    else if (sel[0] == 1'b1)
             reg_out <= in2;

         else if (sel[1] == 1'b0)
                  reg_out <= in3;

              else if (sel[1] == 1'b1)
                       reg_out <= in4;

    endaction

  endmethod

  method out();
    out = reg_out;
  endmethod

endmodule: mkAlternate

endpackage: Alternate
