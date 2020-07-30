interface Ifc;
   interface Inout#(Bool) io;
endinterface

(* synthesize *)
module mkModparamInoutRename
          #((*parameter="io"*)parameter int n)
          (Inout#(Bool) ii, Ifc i);
   interface io = ii;
endmodule

