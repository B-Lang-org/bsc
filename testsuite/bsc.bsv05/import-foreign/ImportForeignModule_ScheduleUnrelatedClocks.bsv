
interface Ifc;
   method Bool m1();
   method Bool m2();
endinterface

import "BVI" Mod =
module mkMod #(Clock c2) (Ifc);
   default_clock c1();
   default_reset no_reset;
   
   input_clock c2() = c2;

   method OUT1 m1();
   method OUT2 m2() clocked_by(c2);

   schedule m1 CF m1;
   schedule m2 CF m2;

   // this should not be allowed
   schedule m1 SB m2;
endmodule

