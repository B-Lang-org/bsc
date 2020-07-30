////////////////////////////////////////////////////////////////////////////////
//  Description   : Top level BSV
////////////////////////////////////////////////////////////////////////////////

// Notes :

////////////////////////////////////////////////////////////////////////////////
/// Imports
////////////////////////////////////////////////////////////////////////////////
import GrayCounter       ::*;
import Clocks            ::*;

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///
/// Implementation
///
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
(* synthesize *)
module sysGrayCounterTest();

   ////////////////////////////////////////////////////////////////////////////////
   /// Clocks / Reset
   ////////////////////////////////////////////////////////////////////////////////
   Clock                                     clkD                <- mkAbsoluteClock(4, 40);
   Reset                                     rstD                <- mkAsyncResetFromCR(3, clkD);

   ////////////////////////////////////////////////////////////////////////////////
   /// Design Elements
   ////////////////////////////////////////////////////////////////////////////////
   Reg#(Bool)                                canFinish           <- mkReg(False);
   
   GrayCounter#(8)                           counterA            <- mkGrayCounter(unpack(0), clkD, rstD);
   GrayCounter#(8)                           counterB            <- mkGrayCounter(unpack(0), clkD, rstD);

   Reg#(Bit#(8))                             counterC            <- mkReg(0);
   Reg#(Bit#(8))                             counterD            <- mkReg(0);
   
   ////////////////////////////////////////////////////////////////////////////////
   /// Rules
   ////////////////////////////////////////////////////////////////////////////////
   (* no_implicit_conditions, fire_when_enabled *)
   rule every;
      counterA.incr;
      counterB.decr;
      counterC <= counterC + 1;
      counterD <= counterD - 1;
      $display("[%x] %x  |  [%x] %x", counterA.sReadGray, counterC, counterB.sReadGray, counterD);
   endrule
   
   (* no_implicit_conditions, fire_when_enabled *)
   rule counterA_counterC_mismatch(counterA.sReadBin != counterC);
      $display("ERROR: counterA mismatch!  %x -> %x != %x", counterA.sReadGray, counterA.sReadBin, counterC);
   endrule
   
   (* no_implicit_conditions, fire_when_enabled *)
   rule counterB_counterD_mismatch(counterB.sReadBin != counterD);
      $display("ERROR: counterB mismatch!  %x -> %x != %x", counterB.sReadGray, counterB.sReadBin, counterD);
   endrule
   
   rule set_can_finish(!canFinish && counterC == 1);
      canFinish <= True;
   endrule
   
   rule finish(canFinish && counterC == 0);
      $finish;
   endrule

endmodule

