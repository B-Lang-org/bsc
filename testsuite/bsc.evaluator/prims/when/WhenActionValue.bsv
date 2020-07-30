(* synthesize *)
module sysWhenActionValue();
   SubIfc s <- mkWhenActionValue_Sub();

   rule r;
      Bool b <- s.m;
      when(b, $display("True"));
   endrule
endmodule

interface SubIfc;
   method ActionValue#(Bool) m();
endinterface

(* synthesize *)
module mkWhenActionValue_Sub(SubIfc);
   Reg#(Bool) rg <- mkReg(True);

   method ActionValue#(Bool) m();
      rg <= !rg;
      return rg;
   endmethod
endmodule

