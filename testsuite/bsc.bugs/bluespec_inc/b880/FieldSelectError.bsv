import FIFO::*;

module mkTest();

  Reg#(Bit#(32)) r <- mkRegU;

  rule test;
    r.deq;
  endrule

endmodule
