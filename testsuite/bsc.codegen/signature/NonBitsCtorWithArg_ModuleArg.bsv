// This type is not in Bits and it has an argument
typedef struct { Integer f1; t f2; } S#(type t);

(* synthesize *)
module sysNonBitsCtorWithArg_ModuleArg #(S#(Bool) x) ();
   Reg#(Bool) b <- mkReg(True);
   rule r;
      b <= b && x.f2 && (x.f1 > 10);
      $display(b);
   endrule
endmodule

