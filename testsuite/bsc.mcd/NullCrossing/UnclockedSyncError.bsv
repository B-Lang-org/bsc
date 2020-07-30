import Clocks::*;

interface Source;
   method UInt#(16) value();
endinterface

(* synthesize *)
module mkSource(Clock dst, Clock bad, Source ifc);

   
   let a = 5;
   
   let b = 7;
   
   UInt#(16) a_plus_b = a + b;
   
   ReadOnly#(UInt#(16)) syncAB <- mkNullCrossingWire(dst, a_plus_b);

   method value = syncAB;
      
endmodule
