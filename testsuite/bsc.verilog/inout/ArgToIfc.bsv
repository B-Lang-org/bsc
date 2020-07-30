interface InoutIFC;
   interface Inout#(int) i_out;
endinterface

(* synthesize *)
module sysArgToIfc #(Inout#(int) i_in) (InoutIFC);
   interface i_out = i_in;
endmodule

