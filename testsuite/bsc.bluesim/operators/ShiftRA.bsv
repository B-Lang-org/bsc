import StmtFSM::*;

(* synthesize *)
module sysShiftRA ();

  // 8
  // 32
  // 64
  // wide
  let wideSize = 128;

  Reg#(Int#(8))   int8    <- mkRegU;
  Reg#(Int#(32))  int32   <- mkRegU;
  Reg#(Int#(64))  int64   <- mkRegU;
  Reg#(Int#(128)) intWide <- mkRegU;

  Reg#(Bit#(8))   idx8    <- mkRegU;
  Reg#(Bit#(32))  idx32   <- mkRegU;
  Reg#(Bit#(64))  idx64   <- mkRegU;
  Reg#(Bit#(128)) idxWide <- mkRegU;

  function Action doShiftRA(Reg#(Int#(datasz)) dataReg,
                            Reg#(Bit#(idxsz)) idxReg);
   action
      Int#(datasz) res = dataReg >> idxReg;
      $display("Shifting right (arith) data size %d with index size %d: %h",
               valueOf(datasz), valueOf(idxsz), res);
      dataReg <= res;
   endaction
  endfunction

  Stmt testseq =
  seq

     action idx8 <= 1; idx32 <= 2; idx64 <= 3; idxWide <= 4; endaction

     // Data 8
     int8 <= minBound; $display("Initial value %h", int8);
     int8 <= minBound; doShiftRA(int8, idx8);
     int8 <= minBound; doShiftRA(int8, idx32);
     int8 <= minBound; doShiftRA(int8, idx64);
     int8 <= minBound; doShiftRA(int8, idxWide);

     int8 <= maxBound; $display("Initial value %h", int8);
     int8 <= maxBound; doShiftRA(int8, idx8);
     int8 <= maxBound; doShiftRA(int8, idx32);
     int8 <= maxBound; doShiftRA(int8, idx64);
     int8 <= maxBound; doShiftRA(int8, idxWide);

     // Data 32
     int32 <= minBound; $display("Initial value %h", int32);
     int32 <= minBound; doShiftRA(int32, idx8);
     int32 <= minBound; doShiftRA(int32, idx32);
     int32 <= minBound; doShiftRA(int32, idx64);
     int32 <= minBound; doShiftRA(int32, idxWide);

     int32 <= maxBound; $display("Initial value %h", int32);
     int32 <= maxBound; doShiftRA(int32, idx8);
     int32 <= maxBound; doShiftRA(int32, idx32);
     int32 <= maxBound; doShiftRA(int32, idx64);
     int32 <= maxBound; doShiftRA(int32, idxWide);

     // Data 64
     int64 <= minBound; $display("Initial value %h", int64);
     int64 <= minBound; doShiftRA(int64, idx8);
     int64 <= minBound; doShiftRA(int64, idx32);
     int64 <= minBound; doShiftRA(int64, idx64);
     int64 <= minBound; doShiftRA(int64, idxWide);

     int64 <= maxBound; $display("Initial value %h", int64);
     int64 <= maxBound; doShiftRA(int64, idx8);
     int64 <= maxBound; doShiftRA(int64, idx32);
     int64 <= maxBound; doShiftRA(int64, idx64);
     int64 <= maxBound; doShiftRA(int64, idxWide);

     // Data Wide
     intWide <= minBound; $display("Initial value %h", intWide);
     intWide <= minBound; doShiftRA(intWide, idx8);
     intWide <= minBound; doShiftRA(intWide, idx32);
     intWide <= minBound; doShiftRA(intWide, idx64);
     intWide <= minBound; doShiftRA(intWide, idxWide);

     intWide <= maxBound; $display("Initial value %h", intWide);
     intWide <= maxBound; doShiftRA(intWide, idx8);
     intWide <= maxBound; doShiftRA(intWide, idx32);
     intWide <= maxBound; doShiftRA(intWide, idx64);
     intWide <= maxBound; doShiftRA(intWide, idxWide);

  endseq;

  mkAutoFSM(testseq);

endmodule
