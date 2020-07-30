
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
// Test mkIfThenElse, mkBuffer_n, mkCompose, mkFn_to_Pipe_Buffered

(* synthesize *)
module [Module] sysIfThenElse (Empty);

   Integer n_samples = 16;
   Integer ifte_latency = 8;

   // ---- Stimulus input: series of ints: 0, 1, 2, ....
   //      with boolean True whenever lower two bits are 11
   Reg #(int)                    in_r        <- mkReg (0);
   FIFOF #(Tuple2 #(int, Bool))  dut_inputs  <- mkPipelineFIFOF;
   FIFO  #(Tuple2 #(int, Bool))  test_inputs <- mkSizedFIFO (10); // >= latency of dut

   rule rl_stimulus;
      if (in_r == 0) $display ("Cycle %0d: Test start: mkIfThenElse", cyclenum ());

      let next_input = tuple2 (in_r, ((pack (in_r) & 3) == 3));
      dut_inputs.enq (next_input);
      test_inputs.enq (next_input);
      in_r <= in_r + 1;
   endrule

   PipeOut #(Tuple2 #(int, Bool)) po_in = f_FIFOF_to_PipeOut (dut_inputs);

   // ---------------- The dut
   // ---- T pipe

   Pipe #(int, int) pt1 = mkFn_to_Pipe (f_incr_by (100));
   Pipe #(int, int) pt2 = mkBuffer_n (ifte_latency);
   Pipe #(int, int) pt  = mkCompose (pt1, pt2);

   // ---- F pipe
   Pipe #(int, int) pf  = mkFn_to_Pipe_Buffered (False, f_incr_by (10), True);

   PipeOut #(int) po_out <- mkIfThenElse (ifte_latency, pt, pf, po_in);

   // ---- Collect output and check
   Reg #(int) j_out <- mkReg (0);

   rule checkOutput;
      match { .in_i, .in_b } = test_inputs.first (); test_inputs.deq ();
      let expected_out = (in_b ? f_incr_by (100) : f_incr_by (10)) (in_i);
      
      let actual_out = po_out.first ();  po_out.deq ();

      $display ("Cycle %0t: Out [%0d]: expected (%0d), actual (%0d)",
                cyclenum (), j_out, expected_out, actual_out);

      if (expected_out != actual_out) begin
         $display ("Cycle %0d: Test fail: mkIfThenElse", cyclenum ());
         $finish;
      end

      if (j_out  == fromInteger (n_samples - 1)) begin
         $display ("Cycle %0d: Test ok: mkIfThenElse: all %0d outputs ok", cyclenum (), n_samples);
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
