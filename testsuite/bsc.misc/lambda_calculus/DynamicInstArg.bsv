interface Ifc;
   method Bool m();
endinterface

(* synthesize *)
module mkDynamicInstArg_Sub (Bool b, Empty ifc);
endmodule

(* synthesize *)
module sysDynamicInstArg ();
   Reg#(Bool) rg <- mkRegU;
   Empty i <- mkDynamicInstArg_Sub(rg);
endmodule
