// test of fundeps in expression being selected by a field (tiSelect)
// using a larger chain of dependencies

import FIFO::*;
import FIFOF::*;
import List::*;

typedef Bit#(8) DataT;

module test (Empty);

  FIFO#(DataT) inbounds [3][4][5][6][7];

  function Action updateCounts (Integer n, Integer m);
    action
      (inbounds[n][m][n][m][n]).deq;
    endaction
  endfunction

endmodule: test

