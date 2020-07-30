interface Ifc;
   method ActionValue#(int) m();
endinterface

(* synthesize *)
(* always_ready, always_enabled *)
module mkAlwaysEnabledAV_Sub2(Ifc);
   Reg#(int) rg <- mkReg(0);
   method ActionValue#(int) m();
      rg <= rg + 1;
      return rg;
   endmethod
endmodule

(* synthesize *)
(* always_ready, always_enabled *)
module mkAlwaysEnabledAV_Sub(Ifc);
   Ifc s <- mkAlwaysEnabledAV_Sub2;
   method ActionValue#(int) m();
      int tmp <- s.m();
      return tmp;
   endmethod
endmodule

(* synthesize *)
module sysAlwaysEnabledAV ();
   Ifc t <- mkAlwaysEnabledAV_Sub;

   rule disp;
      let r <- t.m;
      $display("result: %h", r);
   endrule
endmodule

