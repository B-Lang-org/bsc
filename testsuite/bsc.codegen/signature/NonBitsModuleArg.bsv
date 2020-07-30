// This doesn't have "deriving(Bits)"
typedef struct {
    Bool f1;
    Bool f2;
} S;

(* synthesize *)
module sysNonBitsModuleArg #(S x) ();
   Reg#(Bool) b <- mkReg(True);
   rule r;
      b <= b && x.f1;
      $display(b);
   endrule
endmodule

