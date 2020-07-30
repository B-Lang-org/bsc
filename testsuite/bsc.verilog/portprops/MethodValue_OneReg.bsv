interface Ifc;
   method Bit#(16) m();
endinterface

(* synthesize *)
module sysMethodValue_OneReg (Ifc);
   Reg#(Bit#(16)) rg <- mkReg(17);
   method m = rg;
endmodule

