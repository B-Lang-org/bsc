// Method port conflicting with the port of an input reset argument

interface Ifc;
   (* result = "RST_N_r" *)
   method UInt#(8) m();
endinterface

(* synthesize *)
module mkInputResetMethod (Reset r, Ifc i);
   Reg#(UInt#(8)) ctr <- mkReg(0, reset_by r);

   method m = ctr;
endmodule
