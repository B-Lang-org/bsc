
interface ClkGen ;
   interface Clock clkOut ;
endinterface

import "BVI"
module mkMod (ClkGen);
   output_clock clkOut (CLK_OUT);
endmodule

interface Ifc ;
   interface Clock clkOut ;
   (* always_ready *)
   interface Reg#(int) regi ;
endinterface

(* synthesize *)
module mkOuthighGateAsCondition_Sub ( Ifc );
   ClkGen cg <- mkMod();
   Clock c = cg.clkOut;

   Reg#(int)  r <- mkRegU(clocked_by c) ;
   
   interface clkOut = cg.clkOut ;
   interface regi = r ;
endmodule

(* synthesize *)
module sysOuthigGateAsCondition ( Ifc );

   Ifc c <- mkOuthighGateAsCondition_Sub;
   
   interface clkOut = c.clkOut ;
   interface regi = c.regi ;
   
endmodule
