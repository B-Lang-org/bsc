interface Ifc;
   interface Reset rst_out;
endinterface

(* synthesize *)
module sysIfc_Reset_Case(Reset r1, Reset r2, Reset r3, Ifc ifc);

   Reg#(Bit#(2)) idx <- mkReg(0);

   Reset r;
   case (idx)
      0 : r = r1;
      1 : r = r2;
      2 : r = r3;
      default : r = noReset;
   endcase

   interface rst_out = r;

endmodule

