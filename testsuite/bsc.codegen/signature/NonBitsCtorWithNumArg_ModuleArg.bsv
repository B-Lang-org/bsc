// This type is not in Bits and it has an argument
typedef struct { Integer f1; Bit#(t) f2; } S#(type t);

(* synthesize *)
module sysNonBitsCtorWithNumArg_ModuleArg #(S#(8) x) ();
   Reg#(Bool) b <- mkReg(True);
   rule r;
      b <= b && (x.f2 < 10) && (x.f1 > 10);
      $display(b);
   endrule
endmodule

