interface Ifc;
   method Bit#(16) m();
endinterface

(* synthesize *)
module sysMethodValue_ConcatRegAndConst (Ifc);
   Reg#(Bit#(8)) rg <- mkReg(17);
   method m = {rg, 2};
endmodule

