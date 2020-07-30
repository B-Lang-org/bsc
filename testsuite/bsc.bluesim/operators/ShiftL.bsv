import StmtFSM::*;

(* synthesize *)
module sysShiftL ();

  // 8
  // 32
  // 64
  // wide
  let wideSize = 128;

  Reg#(Bit#(8))   rg8    <- mkRegU;
  Reg#(Bit#(32))  rg32   <- mkRegU;
  Reg#(Bit#(64))  rg64   <- mkRegU;
  Reg#(Bit#(128)) rgWide <- mkRegU;

  Reg#(Bit#(8))   idx8    <- mkRegU;
  Reg#(Bit#(32))  idx32   <- mkRegU;
  Reg#(Bit#(64))  idx64   <- mkRegU;
  Reg#(Bit#(128)) idxWide <- mkRegU;

  function Action doShiftL(Reg#(Bit#(datasz)) dataReg,
                           Reg#(Bit#(idxsz)) idxReg);
   action
      Bit#(datasz) res = dataReg << idxReg;
      $display("Shifting left data size %d with index size %d: %h",
               valueOf(datasz), valueOf(idxsz), res);
      dataReg <= res;
   endaction
  endfunction

  Stmt testseq =
  seq

     action idx8 <= 1; idx32 <= 2; idx64 <= 3; idxWide <= 4; endaction

     // Data 8
     rg8 <= '1; $display("Initial value %h", rg8);
     rg8 <= '1; doShiftL(rg8, idx8);
     rg8 <= '1; doShiftL(rg8, idx32);
     rg8 <= '1; doShiftL(rg8, idx64);
     rg8 <= '1; doShiftL(rg8, idxWide);

     // Data 32
     rg32 <= '1; $display("Initial value %h", rg32);
     rg32 <= '1; doShiftL(rg32, idx8);
     rg32 <= '1; doShiftL(rg32, idx32);
     rg32 <= '1; doShiftL(rg32, idx64);
     rg32 <= '1; doShiftL(rg32, idxWide);

     // Data 64
     rg64 <= '1; $display("Initial value %h", rg64);
     rg64 <= '1; doShiftL(rg64, idx8);
     rg64 <= '1; doShiftL(rg64, idx32);
     rg64 <= '1; doShiftL(rg64, idx64);
     rg64 <= '1; doShiftL(rg64, idxWide);

     // Data Wide
     rgWide <= '1; $display("Initial value %h", rgWide);
     rgWide <= '1; doShiftL(rgWide, idx8);
     rgWide <= '1; doShiftL(rgWide, idx32);
     rgWide <= '1; doShiftL(rgWide, idx64);
     rgWide <= '1; doShiftL(rgWide, idxWide);

  endseq;

  mkAutoFSM(testseq);

endmodule
