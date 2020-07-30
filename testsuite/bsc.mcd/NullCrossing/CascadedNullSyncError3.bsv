import Clocks::*;

interface Source;
   method UInt#(16) value();
endinterface

(* synthesize *)
module mkSource(Clock dst, Source ifc);

   Reg#(UInt#(16)) regA <- mkReg(0);

   UInt#(16) a_plus_2 = regA + 2;
   
   ReadOnly#(UInt#(16)) syncAB <- mkNullCrossingWire(dst, a_plus_2);

   rule incrA;
      regA <= regA + 1;
   endrule: incrA

   rule done (regA > 15);
      $finish(0);
   endrule: done
      
   method value = syncAB;
      
endmodule

(* synthesize *)
module mkMid(Clock dst, Source ifc);

   Source source <- mkSource(dst);

   method UInt#(16) value();
      return source.value() + 8;
   endmethod: value

endmodule: mkMid

(* synthesize *)
module sysCascadedNullSyncError3();
   
   Clock clk  <- exposeCurrentClock();
   Clock clk2 <- mkAbsoluteClock(9,17);
   
   Source mid <- mkMid(clk2);

   Reg#(UInt#(16)) regC <- mkReg(0);
   
   ReadOnly#(UInt#(16)) syncBC <- mkNullCrossingWire(clk, mid.value(), clocked_by clk2);
   
   rule display;
      regC <= syncBC;
      $display("regC = %d", regC);
   endrule: display
   
endmodule: sysCascadedNullSyncError3
