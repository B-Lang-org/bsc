interface Ifc;
   interface Inout#(Bool) out_io;
endinterface

(* synthesize *)
module sysInoutPortAttribute ((*port="p"*) Inout#(Bool) in_io, Ifc i);
   interface out_io = in_io;
endmodule

