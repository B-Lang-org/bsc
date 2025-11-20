

interface Ifc;
   interface Reset rst_out;
endinterface

(* synthesize *)
module sysDeriveResetClock_InputOutputResetUnused#(Reset rst_in) (Ifc);

   interface rst_out = rst_in;

endmodule
