package MkCompletionBuffer;

import CompletionBuffer::*;
import GetPut::*;

module mkDesign(CompletionBuffer#(2,Int #(8)));

  CompletionBuffer#(2,Int #(8)) dut();
  mkCompletionBuffer the_dut(dut);
  return(dut);
endmodule: mkDesign

endpackage: MkCompletionBuffer
