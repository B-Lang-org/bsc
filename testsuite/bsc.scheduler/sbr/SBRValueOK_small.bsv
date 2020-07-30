import Vector::*;
import SBRCount::*;

(* synthesize *)
module sysSBRValueOK_small();

  Vector#(16, Count) counters <- replicateM(mkSBRCount);

  Reg#(UInt#(9)) j <- mkReg(0);

  rule test;
    $display(counters[j].readCount);
    counters[j+1].incCount;
  endrule

endmodule

