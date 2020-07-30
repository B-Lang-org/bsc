interface Ifc;
   interface Reset rst_out;
endinterface

(* synthesize *)
module sysIfc_Reset_ArrSel(Reset r1, Reset r2, Reset r3, Ifc ifc);

   Reg#(Bit#(2)) idx <- mkReg(0);

   Reset rs[4];
   rs[0] = r1;
   rs[1] = r2;
   rs[2] = r3;
   rs[3] = noReset;

   interface rst_out = rs[idx];

endmodule

