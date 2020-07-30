import FIFO::*;
import RegFile::*;
import BRAM::*;
import DefaultValue::*;

(* synthesize *)
module sysPrimMods();
   Reg#(Bool)      rg0 <- mkReg(True);
   Reg#(UInt#(5))  rg1 <- mkRegU;
   Reg#(Bit#(8))   rg2 <- mkRegA(0);

   Reg#(Bool)      crg0[3] <- mkCReg(3, True);
   Reg#(UInt#(5))  crg1[4] <- mkCRegU(4);
   Reg#(Bit#(8))   crg2[5] <- mkCRegA(5, 0);

   RWire#(Bit#(17)) rw0 <- mkRWire;
   // zero-size
   RWire#(Bit#(0))  rw1 <- mkRWire;

   FIFO#(Bool)       f0 <- mkFIFO;
   FIFO#(UInt#(32))  f1 <- mkFIFO1;
   FIFO#(Bit#(3))    f2 <- mkSizedFIFO(4);
   FIFO#(Int#(4))    f3 <- mkLFIFO;
   // zero-sized
   FIFO#(Bit#(0))    f4 <- mkFIFO;
   FIFO#(Bit#(0))    f5 <- mkFIFO1;
   FIFO#(Bit#(0))    f6 <- mkSizedFIFO(4);
   FIFO#(Bit#(0))    f7 <- mkLFIFO;

   RegFile#(Bit#(7), Bit#(12)) rf0 <- mkRegFileFull;
   RegFile#(Bit#(4), Bit#(9))  rf1 <- mkRegFileFullLoad("rf1.txt");

   BRAM_Configure cfg = defaultValue;
   BRAM_Configure cfg_load = defaultValue;
   cfg_load.loadFormat = tagged Hex "bram.txt";

   BRAM1Port#(Bit#(3), Bit#(5))       br0 <- mkBRAM1Server(cfg);
   BRAM1Port#(Bit#(4), Bit#(6))       br1 <- mkBRAM1Server(cfg_load);
   BRAM1PortBE#(Bit#(5), Bit#(16), 2) br2 <- mkBRAM1ServerBE(cfg);
   BRAM1PortBE#(Bit#(6), Bit#(32), 4) br3 <- mkBRAM1ServerBE(cfg_load);

   BRAM2Port#(Bit#(3), Bit#(5))       br4 <- mkBRAM2Server(cfg);
   BRAM2Port#(Bit#(4), Bit#(6))       br5 <- mkBRAM2Server(cfg_load);
   BRAM2PortBE#(Bit#(5), Bit#(16), 2) br6 <- mkBRAM2ServerBE(cfg);
   BRAM2PortBE#(Bit#(6), Bit#(32), 4) br7 <- mkBRAM2ServerBE(cfg_load);

endmodule
