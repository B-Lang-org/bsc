import Clocks::*;

(* synthesize *)
module sysNullSyncTest();
   
   Clock clk  <- exposeCurrentClock();
   Clock clk2 <- mkAbsoluteClock(9,17);
   Reset rst2 <- mkAsyncResetFromCR(2,clk2);
    
   Reg#(UInt#(16)) regA <- mkReg(0);
   Reg#(UInt#(16)) regB <- mkReg(0, clocked_by clk2, reset_by rst2);
   Reg#(UInt#(16)) regC <- mkReg(0);
   
   UInt#(16) a_plus_2 = regA + 2;
   
   ReadOnly#(UInt#(16)) syncAB <- mkNullCrossingWire(clk2, a_plus_2);
   ReadOnly#(UInt#(16)) syncBC <- mkNullCrossingWire(clk, regB, clocked_by clk2);
   
   rule incrA;
      regA <= regA + 1;
   endrule: incrA
   
   rule addB;
      regB <= regB + syncAB;
   endrule: addB
   
   rule display;
      regC <= syncBC;
      $display("regC = %d", regC);
   endrule: display
   
   rule done (regA > 15);
      $finish(0);
   endrule: done
   
endmodule: sysNullSyncTest