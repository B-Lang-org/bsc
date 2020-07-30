interface Ifc;
   method Bit#(16) m();
endinterface

(* synthesize *)
module sysMethodValue_ConcatTwoReg (Ifc);
   Reg#(Bit#(8)) rg1 <- mkReg(17);
   Reg#(Bit#(8)) rg2 <- mkReg(2);
   method m = {rg1, rg2};
endmodule

