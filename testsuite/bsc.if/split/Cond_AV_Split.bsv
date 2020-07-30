interface Ifc;
   method ActionValue#(Bool) avmeth();
endinterface

(* synthesize *)
module mkCond_AV_Split_Sub(Ifc);
   Reg#(Bool) rg <- mkRegU;

   method ActionValue#(Bool) avmeth();
      return rg;
   endmethod
endmodule

(* synthesize *)
module sysCond_AV_Split();
   Ifc m <- mkCond_AV_Split_Sub;

   rule r;
      Bool b <- m.avmeth;
      (* split *)
      if (b)
         $display("True");
      else
         $display("False");
   endrule
endmodule

