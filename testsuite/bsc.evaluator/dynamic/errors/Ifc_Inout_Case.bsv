interface Ifc;
   interface Inout#(Bool) io_out;
endinterface

(* synthesize *)
module sysIfc_Inout_Case
          (Inout#(Bool) io1, Inout#(Bool) io2,
           Inout#(Bool) io3, Inout#(Bool) io4,
           Ifc ifc);

   Reg#(Bit#(2)) idx <- mkReg(0);

   Inout#(Bool) io;
   case (idx)
      0 : io = io1;
      1 : io = io2;
      2 : io = io3;
      default : io = io4;
   endcase

   interface io_out = io;

endmodule

