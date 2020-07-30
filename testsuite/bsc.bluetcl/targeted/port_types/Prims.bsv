// Test that the port types and ifc hierarchy is properly reported for
// Bluespec primitives (which are often composed of hidden layers and require
// specific support in Bluetcl to map between the visible ifc and the ports)

import RegFile::*;
import FIFO::*;
import FIFOF::*;

import Clocks::*;

(* synthesize *)
module sysPrims ();

  // ----------
  // Registers

  Reg#(int) rg <- mkReg(0);
  Reg#(int) rgA <- mkRegA(0);
  Reg#(int) rgU <- mkRegU();

  // ----------
  // Wires

  RWire#(int) rw <- mkRWire();
  RWire#(Bit#(0)) rw0 <- mkRWire();
  Wire#(int) w <- mkWire();
  Wire#(int) dw <- mkDWire(0);
  Wire#(int) bw <- mkBypassWire();
  PulseWire pw <- mkPulseWire();
  PulseWire pwo <- mkPulseWireOR();

  // ----------
  // RegFile

  RegFile#(Bit#(2), int) rf <- mkRegFileFull;

  // ----------
  // FIFOF

  FIFOF#(int) ff1 <- mkFIFOF;
  // XXX could test more FIFOF

  // ----------
  // FIFO

  // FIFO1
  FIFO#(int) f1 <- mkFIFO1;
  FIFO#(Bit#(0)) f10 <- mkFIFO1;

  // FIFO2
  FIFO#(int) f2 <- mkFIFO;
  FIFO#(Bit#(0)) f20 <- mkFIFO;

  // SizedFIFO
  FIFO#(int) fs <- mkSizedFIFO(16);
  FIFO#(Bit#(0)) fs0 <- mkSizedFIFO(16);

  // Loopy FIFO1
  FIFO#(int) fL1 <- mkLFIFO;
  FIFO#(Bit#(0)) fL10 <- mkFIFO;

  // XXX could test Loopy FIFO2 and SizedFIFO

  // ----------
  // Clocks library

  Clock dclk <- mkAbsoluteClock(15, 15);

  // SyncReg is specially handled in Bluetcl
  Reg#(int) sr <- mkSyncRegFromCC(0, dclk);

  // clock crossing BypassWire is specially handled
   Tuple2#(Wire#(int), Maybe#(Name__)) bcw <- mkBypassCrossingWire(dclk);

   // null crossing wire uses mkBypassCrossingWire
   ReadOnly#(Int#(32)) ncw <- mkNullCrossingWire( dclk, rgA );
   
  // XXX other prims are not specially handled, but should be tested

   rule do_always_enable_methods (True);
      bw._write(4);
      tpl_1(bcw)._write(50);
   endrule

endmodule


