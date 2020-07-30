
(* synthesize *)
module sysInhighEnable ();
  Reg#(Bool) rg1 <- mkInhighEnable_BVI;
  Reg#(Bool) rg2 <- mkInhighEnable_Sub;

  // silence warnings about the enables
  rule r;
    rg1 <= !rg1;
    rg2 <= !rg2;
  endrule
endmodule


import "BVI" MOD =
module mkInhighEnable_BVI(Reg#(a) ifc)
   provisos (Bits#(a, sa)) ;

   method D_OUT _read() ;
   method _write(Q_IN) enable((*inhigh*)EN) ;

   schedule   _read CF _read ;
   schedule   _read SB _write ;
   schedule   _write SBR _write ;
endmodule


(* synthesize,
   always_ready,
   always_enabled="_write" *)
module mkInhighEnable_Sub(Reg#(Bool));
   Reg#(Bool) rg <- mkRegU;
   return rg;
endmodule
