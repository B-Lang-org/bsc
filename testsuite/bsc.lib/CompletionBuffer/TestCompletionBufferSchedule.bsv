
import CompletionBuffer :: *;

(* synthesize *)
module mkCompletionBuffer_4_Bit32 (CompletionBuffer#(4, Bit#(32)));
   (* hide *)
   let _ifc <- mkCompletionBuffer;
   return _ifc;
endmodule

