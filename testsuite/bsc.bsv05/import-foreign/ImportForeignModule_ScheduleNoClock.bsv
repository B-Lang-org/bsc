
interface Ifc;
   method Bool m1();
   method Bool m2();
endinterface

import "BVI" Mod =
module mkMod (Ifc);
   default_clock no_clock;
   default_reset no_reset;
   
   method OUT1 m1();
   method OUT2 m2();

   schedule m1 CF m1;
   schedule m2 CF m2;

   // this should not be allowed
   schedule m1 SB m2;
endmodule

