import Clocks::*;

import "BVI" CrossingRegN =
module vMkNullCrossingRegL( Clock dstClk, a initVal, CrossingReg#(a) ifc )
   provisos (Bits#(a, sz_a)) ;

   default_clock sClk (CLK);
   default_reset sRst (RST_N);

   parameter width = valueOf(sz_a) ;
   parameter init  = pack(initVal);

   input_clock dClk() = dstClk;

   method _write(D_IN) enable(EN) clocked_by(sClk) reset_by(sRst);
   method Q_OUT _read() clocked_by(sClk) reset_by(sRst) ;
   method Q_OUT crossed() clocked_by(dClk) reset_by(no_reset) ;

   schedule   _write  SBR  _write ;
   schedule   _read   CF _read ;
   schedule   _read   SB _write;
   schedule   crossed CF crossed ;
endmodule

(* synthesize *)
module sysPrimitiveBVI_BadPortName (Clock clk2, Empty ifc);
   CrossingReg#(Bool) rg <- vMkNullCrossingRegL(clk2, False);

   rule set;
     rg <= True;
   endrule

   rule get;
     if (rg)
       $finish(0);
   endrule
endmodule
