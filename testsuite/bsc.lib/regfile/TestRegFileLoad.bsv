import RegFile::*;

(* synthesize *)
module sysTestRegFileLoad(Empty);
  RegFile#(Bit#(2), Bit#(4)) regs  <- mkRegFileLoad("TestRegFileLoad.hex.input", 0, 3);
  RegFile#(Bit#(2), Bit#(4)) regsH <- mkRegFileLoadHex("TestRegFileLoad.hex.input", 0, 3);
  RegFile#(Bit#(3), Bit#(8)) regsB <- mkRegFileLoadBin("TestRegFileLoad.bin.input", 0, 7);
  Reg#(Bit#(5)) pos <- mkReg(0);

  rule printBin(pos < 8);
    $display(regsB.sub(truncate(pos)));
    pos <= pos+1;
  endrule
  
  rule printHex(pos >= 8 && pos < 12);
    $display(regsH.sub(truncate(pos)));
    pos <= pos+1;
  endrule

  rule print(pos >= 12 && pos < 16);
    $display(regs.sub(truncate(pos)));
    pos <= pos+1;
  endrule

  rule stopSimulation(pos >= 16);
    $finish(0);
  endrule
endmodule


