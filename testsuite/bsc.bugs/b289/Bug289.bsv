import FIFO::*;

module blah();
  FIFO::FIFO#(Bool) outbound();
  FIFO::mkFIFO the_outbound1(outbound);
endmodule
