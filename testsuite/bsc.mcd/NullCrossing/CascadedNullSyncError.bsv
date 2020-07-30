import Clocks::*;

(* synthesize *)
module sysCascadedNullSyncError();
   
   Clock clk  <- exposeCurrentClock();
   Clock clk2 <- mkAbsoluteClock(9,17);
    
   Reg#(UInt#(16))  regA  <- mkReg(0);
   Reg#(UInt#(16))  regC  <- mkReg(0);
   
   UInt#(16) a_plus_2 = regA + 2;
   
   ReadOnly#(UInt#(16)) syncAB <- mkNullCrossingWire(clk2, a_plus_2);
   ReadOnly#(UInt#(16)) syncBC <- mkNullCrossingWire(clk, syncAB, clocked_by clk2);
   
   rule incrA;
      regA <= regA + 1;
   endrule: incrA
   
   rule display;
      regC <= syncBC;
      $display("regC = %d", regC);
   endrule: display
   
   rule done (regA > 15);
      $finish(0);
   endrule: done
   
endmodule: sysCascadedNullSyncError