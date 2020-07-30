interface Sub;
   method Action m(Bit#(16) b);
endinterface

// a submodule with an unused data input port
(* synthesize *)
module mkInputArg_OneRegOneUnused_Sub (Sub);
   method m(b) = noAction;
endmodule

(* synthesize *)
module sysInputArg_OneRegOneUnused #(Bit#(16) b) ();
   Reg#(Bit#(16)) rg <- mkReg(0);
   Sub s <- mkInputArg_OneRegOneUnused_Sub;

   rule r;
      rg <= b;
      s.m(b);
   endrule
endmodule

