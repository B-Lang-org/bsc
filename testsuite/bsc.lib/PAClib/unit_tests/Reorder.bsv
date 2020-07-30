// ----------------------------------------------------------------
// Small, directed tests for the various functions in PAClib
//
// Please comment out all except one test in mkTb_PAClib
// ----------------------------------------------------------------
// Import standard BSV libs

import LFSR::*;
import Vector::*;
import FIFO::*;
import FIFOF::*;
import SpecialFIFOs    ::    *;
import GetPut::*;
import ClientServer::*;
import CompletionBuffer  :: *;

import PAClib::*;
import Common::*;

// ----------------------------------------------------------------




// ================================================================
// Test mkReorder, mkIfThenElse_unordered
// Generates 0,1,2,3,....
// Normally they go through a path of latency 1
// but every 4th one (3, 7, 11, ...)  is sent through a path of latency 10
// Thus, normally they would emerge out-of-order.
// This is encapsulated into mkReorder to restore order

(* synthesize *)
module [Module] sysReorder (Empty);

   Integer n_samples = 16;
   Integer f_latency = 1;
   Integer t_latency  = 3;

   // ---- Stimulus input: series of ints: 0, 1, 2, ....
   //      with boolean True whenever lower two bits are 11
   Reg #(int)         in_r      <- mkReg (0);

   FIFOF #(Tuple2 #(int, Bool))  dut_inputs  <- mkPipelineFIFOF;

   rule rl_stimulus;
      if (in_r == 0) $display ("Cycle %0d: Test start: mkReorder", cyclenum ());

      let next_input = tuple2 (in_r, ((pack (in_r) & 3) == 3));
      dut_inputs.enq (next_input);
      in_r <= in_r + 1;
   endrule

   PipeOut #(Tuple2 #(int, Bool)) po_in = f_FIFOF_to_PipeOut (dut_inputs);

   // ---------------- The dut
   // ---- Retuple from (cb, (x, bool)) to ((cb, x), bool)
   function  Tuple2 #(Tuple2 #(CBToken #(3), int), Bool)
             fn_retuple (Tuple2 #(CBToken #(3), Tuple2 #(int, Bool)) z);
      match { .cb, { .x, .b }} = z;
      return tuple2 (tuple2 (cb, x), b);
   endfunction

   Pipe #(Tuple2 #(CBToken #(3), Tuple2 #(int, Bool)), Tuple2 #(Tuple2 #(CBToken #(3), int), Bool))
      pipe_retuple = mkFn_to_Pipe (fn_retuple);

   // ---- T pipe
   Pipe #(Tuple2 #(CBToken #(3), int), Tuple2 #(CBToken #(3), int)) pt1 = mkFn_to_Pipe (id);
   Pipe #(Tuple2 #(CBToken #(3), int), Tuple2 #(CBToken #(3), int)) pt2 = mkBuffer_n (t_latency);
   Pipe #(Tuple2 #(CBToken #(3), int), Tuple2 #(CBToken #(3), int)) pt  = mkCompose (pt1, pt2);

   // ---- F pipe
   Pipe #(Tuple2 #(CBToken #(3), int), Tuple2 #(CBToken #(3), int)) pf1 = mkFn_to_Pipe (id);
   Pipe #(Tuple2 #(CBToken #(3), int), Tuple2 #(CBToken #(3), int)) pf2 = mkBuffer_n (f_latency);
   Pipe #(Tuple2 #(CBToken #(3), int), Tuple2 #(CBToken #(3), int)) pf  = mkCompose (pf1, pf2);

   // ---- If-then-else unordered
   Pipe #(Tuple2 #(Tuple2 #(CBToken #(3), int), Bool), Tuple2 #(CBToken #(3), int))
      pipe_ifte = mkIfThenElse_unordered (pt, pf);

   // ---- Compose retupling and ifte
   Pipe #(Tuple2 #(CBToken #(3), Tuple2 #(int, Bool)),
          Tuple2 #(CBToken #(3), int)) pipe_body = mkCompose (pipe_retuple, pipe_ifte);

   PipeOut #(int) po_out <- mkReorder (pipe_body, po_in);

   // ---- Collect output and check
   Reg #(int) j_out <- mkReg (0);

   rule checkOutput;
      let expected_out = j_out;
      let actual_out = po_out.first ();  po_out.deq ();

      $display ("Cycle %0t: Out [%0d]: expected (%0d)",
                cyclenum (), j_out, actual_out);

      if (expected_out != actual_out) begin
         $display ("Cycle %0d: Test fail: mkReorder", cyclenum ());
         $finish;
      end

      if (j_out  == fromInteger (n_samples - 1)) begin
         $display ("Cycle %0d: Test ok: mkReorder: all %0d outputs ok", cyclenum (), n_samples);
         $finish;
      end
      else
         j_out <= j_out + 1;
   endrule
endmodule

// ================================================================
// General utilities

// ----------------------------------------------------------------
// Cycle count


// ----------------------------------------------------------------
// Increment by n


// ----------------------------------------------------------------
// Print vector of ints


// ----------------------------------------------------------------
// Print vector of (ints,index) tuples



// ================================================================
