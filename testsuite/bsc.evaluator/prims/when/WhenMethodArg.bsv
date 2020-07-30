(* synthesize *)
module sysWhenMethodArg();
   SubIfc s <- mkWhenMethodArg_Sub();

   Reg#(Bool) rg <- mkReg(True);

   rule r;
      Bool b <- s.m(rg);
      rg <= b;
   endrule
endmodule

interface SubIfc;
   method ActionValue#(Bool) m(Bool b);
endinterface

(* synthesize *)
module mkWhenMethodArg_Sub(SubIfc);
   Reg#(Bool) rg <- mkReg(True);

   method ActionValue#(Bool) m(Bool b);
      when (rg == b, action
                        rg <= !rg;
                     endaction);
      return rg;
   endmethod
endmodule

