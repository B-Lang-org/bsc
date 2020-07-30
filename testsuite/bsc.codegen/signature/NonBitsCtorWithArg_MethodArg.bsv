// This type is not in Bits and it has an argument
typedef struct { Integer f1; t f2; } S#(type t);

interface IFC;
   method Bool m (S#(Bool) x);
endinterface

(* synthesize *)
module sysNonBitsCtorWithArg_MethodArg (IFC);
   method Bool m (S#(Bool) x);
      return (x.f2 && (x.f1 > 10));
   endmethod
endmodule

