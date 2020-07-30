// test of fundeps in expression being selected by a field (tiSelect)

import FIFO::*;
import FIFOF::*;

typedef Bit#(8) DataT;

module test (Empty);

  FIFO#(DataT) inbounds [3];

  for (Integer i = 0; i < 3; i = i + 1)
    inbounds[i] <- mkFIFO;
    
  function Action updateCounts (Integer n);
    action
      (inbounds[n]).deq;
    endaction
  endfunction

endmodule: test

