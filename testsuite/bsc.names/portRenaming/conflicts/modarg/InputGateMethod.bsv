// Method port conflicting with the gate port of an input clock argument

interface Ifc;
   (* result = "CLK_GATE_c" *)
   method UInt#(8) m();
endinterface

(* synthesize *)
(* gate_input_clocks = "c" *)
module mkInputGateMethod (Clock c, Ifc i);
   Reg#(UInt#(8)) ctr <- mkReg(0, clocked_by c, reset_by noReset);

   method m = ctr;
endmodule
