// This type has an argument and is in Bits (if it's argument is in Bits)
typedef struct { t f; } S#(type t) deriving (Bits);

(* synthesize *)
module sysCtorWithNonBitsArg_ModuleArg #(S#(Integer) x) ();
   Reg#(Bool) b <- mkReg(True);
   rule r;
      b <= b && (x.f > 10);
      $display(b);
   endrule
endmodule

