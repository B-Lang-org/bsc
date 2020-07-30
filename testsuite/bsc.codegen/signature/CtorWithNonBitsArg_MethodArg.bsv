// This type has an argument and is in Bits (if it's argument is in Bits)
typedef struct { t f; } S#(type t) deriving (Bits);

interface IFC;
   method Bool m (S#(Integer) x);
endinterface

(* synthesize *)
module sysCtorWithNonBitsArg_MethodArg (IFC);
   method Bool m (S#(Integer) x);
      return x.f > 10;
   endmethod
endmodule

