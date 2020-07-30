import RegFile::*;

(* synthesize *)
module sysRegFileZeroIndex(Empty);

  RegFile#(Bit#(0), Bit#(4)) rf0  <- mkRegFile(0, 0);
  RegFile#(Bit#(0), Bit#(4)) rf0cf  <- mkRegFileWCF(0, 0);

  RegFile#(Bit#(0), Bit#(4)) rf1  <- mkRegFileLoadHex("data.txt", 0, 0);
  RegFile#(Bit#(0), Bit#(4)) rf1cf  <- mkRegFileWCFLoadHex("data.txt", 0, 0);

  RegFile#(Bit#(0), Bit#(4)) rf2  <- mkRegFileLoadBin("data.txt", 0, 0);
  RegFile#(Bit#(0), Bit#(4)) rf2cf  <- mkRegFileWCFLoadBin("data.txt", 0, 0);

  // confirm that the WCF versions are in fact CF
  // (if so, then rules rA and rB will not conflict)

  Reg#(Bool) rg <- mkRegU;

  rule rA;
     // Force "rA SB rB"
     $display(rg);

     // Test that these do not introduce "rB SB rA"
     Bit#(4) val = 'h0;
     rf0cf.upd(0, val);
     rf1cf.upd(0, val);
     rf2cf.upd(0, val);
  endrule

  rule rB;
     // Force "rA SB rB"
     rg <= True;

     // Test that these do not introduce "rB SB rA"
     $display(rf0cf.sub(0));
     $display(rf1cf.sub(0));
     $display(rf2cf.sub(0));
  endrule

endmodule

