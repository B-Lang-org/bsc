interface Ifc;
   interface Reset rst_out;
endinterface

(* synthesize *)
module sysIfc_Reset_If(Reset r1, Reset r2, Ifc ifc);

   Reg#(Bool) b <- mkReg(False);

   interface rst_out = (b ? r1 : r2);

endmodule

