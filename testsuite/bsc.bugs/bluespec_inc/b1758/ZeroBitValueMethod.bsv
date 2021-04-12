
typedef Bit #(0)  T;

interface Ifc#(type t);
   method t getVal();
endinterface

(* synthesize *)
module mkZeroBitValueMethod_Get (Ifc#(T));
endmodule

(* synthesize *)
module sysZeroBitValueMethod ();

   Ifc#(T) g <- mkZeroBitValueMethod_Get;

   rule do_disp;
      let v = g.getVal;
      $display("v = %b", v);
   endrule

endmodule

