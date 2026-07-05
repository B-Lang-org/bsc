// Method port conflicting with the implicit default reset port

interface Ifc;
   (* result = "RST_N" *)
   method UInt#(8) m();
endinterface

(* synthesize *)
module mkDefaultResetMethod (Ifc);
   Reg#(UInt#(8)) ctr <- mkReg(0);

   method m = ctr;
endmodule
