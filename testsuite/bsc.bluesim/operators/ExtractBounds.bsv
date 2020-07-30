import StmtFSM::*;

(* synthesize *)
module sysExtractBounds ();

  // 8
  // 32
  // 64
  // wide
  Reg#(Bit#(8))   rg8    <- mkRegU;
  Reg#(Bit#(32))  rg32   <- mkRegU;
  Reg#(Bit#(64))  rg64   <- mkRegU;
  Reg#(Bit#(128)) rgWide <- mkRegU;
  let wideSize = 128;

  Reg#(Bit#(16))  idx    <- mkRegU;

  function Action doExtract(Reg#(Bit#(fromsz)) fromReg, Reg#(Bit#(tosz)) toReg);
   action
      let lo = 0;
      let hi = idx-1;
      Bit#(tosz) res = fromReg[hi:lo];
      $display("Extracting from size %d to size %d: %h",
               valueOf(fromsz), valueOf(tosz), res);
      toReg <= res;
   endaction
  endfunction

  Stmt testseq =
  seq

     // From 8
     idx <= 8 + 2;
     rg8 <= '1;
     doExtract(rg8, rg8);
     doExtract(rg8, rg32);
     doExtract(rg8, rg64);
     doExtract(rg8, rgWide);

     // From 32
     idx <= 32 + 2;
     rg32 <= '1;
     doExtract(rg32, rg8);
     doExtract(rg32, rg32);
     doExtract(rg32, rg64);
     doExtract(rg32, rgWide);

     // From 64
     idx <= 64 + 2;
     rg64 <= '1;
     doExtract(rg64, rg8);
     doExtract(rg64, rg32);
     doExtract(rg64, rg64);
     doExtract(rg64, rgWide);

     // From wide
     idx <= wideSize + 2;
     rgWide <= '1;
     doExtract(rgWide, rg8);
     doExtract(rgWide, rg32);
     doExtract(rgWide, rg64);
     doExtract(rgWide, rgWide);

  endseq;

  mkAutoFSM(testseq);

endmodule
