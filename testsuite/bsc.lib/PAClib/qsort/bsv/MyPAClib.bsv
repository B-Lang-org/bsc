import PAClib::*;
import FIFOF::*;
import GetPut::*;
import CompletionBuffer::*;

function Tuple2#(Tuple2#(CBToken#(n), a), Bool) replace_tuple (Tuple2#(CBToken#(n), Tuple2#(a, Bool)) in);
   match {.cbtoken, .tWithPred} = in;
   match {.t, .pred} = tWithPred;
   return tuple2(tuple2(cbtoken, t), pred);
endfunction

module [Module] mkIfThenElse_sub
//                #(Pipe #(Tuple2#(CBToken#(n), a), Tuple2#(CBToken#(n), b))  pipeT,
//                  Pipe #(Tuple2#(CBToken#(n), a), Tuple2#(CBToken#(n), b))  pipeF,
                #(function Module #(PipeOut#(Tuple2#(CBToken #(n), b))) pipeT (PipeOut#(Tuple2#(CBToken #(n), a)) ifcT),
                  function Module #(PipeOut#(Tuple2#(CBToken #(n), b))) pipeF (PipeOut#(Tuple2#(CBToken #(n), a)) ifcF),
                  PipeOut#(Tuple2#(CBToken#(n), Tuple2#(a, Bool))) poa)
                (PipeOut#(Tuple2#(CBToken#(n), b)))

        provisos (Bits #(a, sa),
                  Bits #(b, sb));

   let x1 <- mkFn_to_Pipe(replace_tuple, poa);
   let x2 <- mkIfThenElse_unordered(pipeT, pipeF, x1);
   return x2;
endmodule

module [Module] mkIfThenElse_ordered
//                #(Pipe #(Tuple2#(CBToken#(n), a), Tuple2#(CBToken#(n), b))  pipeT,
//                  Pipe #(Tuple2#(CBToken#(n), a), Tuple2#(CBToken#(n), b))  pipeF,
                #(function Module #(PipeOut#(Tuple2#(CBToken #(n), b))) pipeT (PipeOut#(Tuple2#(CBToken #(n), a)) ifcT),
                  function Module #(PipeOut#(Tuple2#(CBToken #(n), b))) pipeF (PipeOut#(Tuple2#(CBToken #(n), a)) ifcF),
                  PipeOut #(Tuple2 #(a, Bool)) poa)
                (PipeOut #(b))

        provisos (Bits #(a, sa),
                  Bits #(b, sb));

//   PipeOut#(b) reordered <- mkReorder(mkIfThenElse_sub(pipeT, pipeF), poa);
   PipeOut#(b) reordered <- mkNewReorder(mkIfThenElse_sub(pipeT, pipeF), poa);
   return reordered;

endmodule: mkIfThenElse_ordered


module [Module] mkNewReorder
//                #(Pipe #(Tuple2 #(CBToken #(n), a), Tuple2 #(CBToken #(n), b)) mkBody,
                #(function Module #(PipeOut#(Tuple2#(CBToken #(n), b))) mkBody (PipeOut#(Tuple2#(CBToken #(n), a)) ifc),
                  PipeOut #(a) po_in)
                (PipeOut #(b))

        provisos (Bits #(a, sa),
                  Bits #(b, sb));

   CompletionBuffer #(n, b) cb <- mkCompletionBuffer;

   FIFOF #(Tuple2 #(CBToken #(n), a)) tagged_inputs <- mkLFIFOF;
   FIFOF #(b)                         outputs       <- mkLFIFOF;

   rule rl_tag_inputs;
      let x      =  po_in.first ();  po_in.deq ();
      let cbtok <-  cb.reserve.get ();
      tagged_inputs.enq (tuple2 (cbtok, x));
   endrule

   let body_out <- mkBody (f_FIFOF_to_PipeOut (tagged_inputs));

   rule rl_drain_body;
      cb.complete.put (body_out.first ());  body_out.deq ();
   endrule

   (* descending_urgency = "rl_drain_cb, rl_tag_inputs" *)

   rule rl_drain_cb;
      let z <- cb.drain.get ();
      outputs.enq (z);
   endrule

   return f_FIFOF_to_PipeOut (outputs);
endmodule: mkNewReorder

