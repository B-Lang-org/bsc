interface Ifc;
   method Bit#(16) m();
endinterface

(* synthesize *)
module sysMethodValue_ExtractReg (Ifc);
   Reg#(Bit#(32)) rg <- mkReg(17);
   method m = truncate(rg);
endmodule

