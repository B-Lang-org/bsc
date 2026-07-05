// Method port conflicting with the implicit default clock port

interface Ifc;
   (* result = "CLK" *)
   method UInt#(8) m();
endinterface

(* synthesize *)
module mkDefaultClockMethod (Ifc);
   Reg#(UInt#(8)) ctr <- mkReg(0);

   method m = ctr;
endmodule
