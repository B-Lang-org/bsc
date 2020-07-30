(* synthesize *)
module mkPortExpr_SubmodPort ();
   Reg#(Bit#(8)) s <- mkRegU;
   IFC i <- mkPortExpr_SubmodPort_Sub(s);
endmodule

interface IFC;
   method Bit#(8) val ();
endinterface

// A module with a dynamic module argument
(* synthesize *)
module mkPortExpr_SubmodPort_Sub#(Bit#(8) p) (IFC);
   Reg#(Bit#(8)) r <- mkReg(0);

   rule inc;
      r <= r + p;
   endrule

   method val = r;
endmodule
