import Vector::*;
import SBRCount::*;

(* synthesize *)
module sysValueNotOK();

  Vector#(512, Count) counters <- replicateM(mkSBRCount);

  Reg#(UInt#(9)) j <- mkReg(0);

  rule test;
    $display(counters[j].readCount);
    counters[j].incCount;
  endrule

endmodule
    