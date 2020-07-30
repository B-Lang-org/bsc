interface Ifc;
   interface Clock clk_out;
endinterface

(* synthesize *)
module sysIfc_Clock_If(Clock c1, Clock c2, Ifc ifc);

   Reg#(Bool) b <- mkReg(False);

   interface clk_out = (b ? c1 : c2);

endmodule

