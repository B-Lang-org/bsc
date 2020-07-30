interface Ifc;
   method Bit#(16) m();
endinterface

(* synthesize *)
module sysMethodValue_Logic (Ifc);
   Reg#(Bit#(16)) rg <- mkReg(17);
   method m = rg + 1;
endmodule

