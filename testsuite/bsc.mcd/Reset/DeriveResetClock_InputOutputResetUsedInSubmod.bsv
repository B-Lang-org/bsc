

interface Ifc;
   interface Reset rst_out;
endinterface

(* synthesize *)
module sysDeriveResetClock_InputOutputResetUsedInSubMod
           #(Clock c2, Reset rst_in) (Ifc);

   Reg#(Bool) rg <- mkReg(True, clocked_by c2, reset_by rst_in);

   // test that the output reset is associated to c2
   interface rst_out = rst_in;

endmodule
