package TaskArg;

// System-task arguments get implicit pack coercions inserted by the
// typechecker; those coercions must force correctly (the held form is
// squeezed when the foreign-call argument is materialized).
typedef struct { Bit#(8) a; Bit#(8) b; } TA deriving (Bits);

(* synthesize *)
module mkTaskArg();
   Reg#(TA) r <- mkRegU;
   Reg#(UInt#(8)) cnt <- mkRegU;
   rule show;
      $display("r=%h cnt=%0d", r, cnt);
   endrule
endmodule

endpackage
