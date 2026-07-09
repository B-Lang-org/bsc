// Method port conflicting with the renamed port of an input clock argument

interface Ifc;
   (* result = "XCLK" *)
   method UInt#(8) m();
endinterface

(* synthesize *)
module mkInputClockRenameMethod ((* osc = "XCLK" *) Clock c, Ifc i);
   Reg#(UInt#(8)) ctr <- mkReg(0, clocked_by c, reset_by noReset);

   method m = ctr;
endmodule
