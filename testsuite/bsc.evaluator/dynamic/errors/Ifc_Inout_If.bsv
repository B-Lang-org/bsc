interface Ifc;
   interface Inout#(Bool) io_out;
endinterface

(* synthesize *)
module sysIfc_Inout_If(Inout#(Bool) io1, Inout#(Bool) io2, Ifc ifc);

   Reg#(Bool) b <- mkReg(False);

   interface io_out = (b ? io1 : io2);

endmodule

