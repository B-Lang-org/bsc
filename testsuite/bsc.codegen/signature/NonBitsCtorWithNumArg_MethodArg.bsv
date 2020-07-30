// This type is not in Bits and it has an argument
typedef struct { Integer f1; Bit#(t) f2; } S#(type t);

interface IFC;
   method Bool m (S#(8) x);
endinterface

(* synthesize *)
module sysNonBitsCtorWithNumArg_MethodArg (IFC);
   method Bool m (S#(8) x);
      return ((x.f2 < 10) && (x.f1 > 10));
   endmethod
endmodule

