import RegFile::*;
import Vector::*;

(* synthesize *)
module sysVecOfRegFile_Sub();

   Reg#(Bit#(1)) idx <- mkRegU;

   Vector#(2, RegFile#(Bit#(3), Bit#(16))) rfs <- replicateM(mkRegFileFull);

  rule r;
   Bit#(16) res = rfs[idx].sub(0);
   $display(res);
 endrule

endmodule

