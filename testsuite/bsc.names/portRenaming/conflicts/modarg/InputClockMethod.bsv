// Method port conflicting with the derived port of an input clock argument

interface Ifc;
   (* result = "CLK_c" *)
   method UInt#(8) m();
endinterface

(* synthesize *)
module mkInputClockMethod (Clock c, Ifc i);
   Reg#(UInt#(8)) ctr <- mkReg(0, clocked_by c, reset_by noReset);

   method m = ctr;
endmodule
