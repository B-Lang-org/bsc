import Clocks::*;

interface Source;
   method UInt#(16) value();
endinterface

(* synthesize *)
module mkSource(Clock dst, Clock bad, Source ifc);

   Reg#(UInt#(16)) regA <- mkReg(0);
   Reg#(UInt#(16)) regB <- mkRegU(clocked_by bad);
   
   UInt#(16) a_plus_b = regA + regB;
   
   ReadOnly#(UInt#(16)) syncAB <- mkNullCrossingWire(dst, a_plus_b);

   rule incrA;
      regA <= regA + 1;
   endrule: incrA

   rule done (regA > 15);
      $finish(0);
   endrule: done
      
   method value = syncAB;
      
endmodule
