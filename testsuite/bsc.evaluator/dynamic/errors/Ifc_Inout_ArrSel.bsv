interface Ifc;
   interface Inout#(Bool) io_out;
endinterface

(* synthesize *)
module sysIfc_Inout_If
          (Inout#(Bool) io1, Inout#(Bool) io2,
           Inout#(Bool) io3, Inout#(Bool) io4,
           Ifc ifc);

   Reg#(Bit#(2)) idx <- mkReg(0);

   Inout#(Bool) ios[4];
   ios[0] = io1;
   ios[1] = io2;
   ios[2] = io3;
   ios[3] = io4;

   interface io_out = ios[idx];

endmodule

