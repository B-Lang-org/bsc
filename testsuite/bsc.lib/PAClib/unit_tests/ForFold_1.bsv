
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
// Test mkForFold 1
// Doesn't actually do any folding, just tests that it is fully pipelined
// in the corner case where the for-iteration count is 1

(* synthesize *)
module [Module] sysForFold_1 (Empty);

   Integer n_samples = 16;

   // ---- Stimulus input: 0,1,2,3, ... with every one paired with "True"

   // Register used to generate inputs
   Reg#(int) count <- mkReg (0);

   FIFOF #(int)  dut_inputs  <- mkPipelineFIFOF;

   rule rl_stimulus;
      if (count == 0) $display ("Cycle %0d: Test start: mkForFold 1", cyclenum ());

      dut_inputs.enq (count);
      count <= count + 1;
   endrule

   PipeOut #(int) po_in = f_FIFOF_to_PipeOut (dut_inputs);

   // ---------------- The dut
   function int  f_combine (Tuple2 #(int, int) xy);
      match { .x1, .x2 } = xy;
      return (x1 + x2);
   endfunction

   let combine_pipe = mkFn_to_Pipe (f_combine);

   UInt #(1) n_items = 1;
   let po_out <- mkForFold (n_items, combine_pipe, po_in);

   // ---------------- Check outputs

   Reg #(int)  n_out <- mkReg (0);

   rule rl_check;
      let expected_y = n_out;

      let actual_y   = po_out.first (); po_out.deq ();

      $display ("Cycle %0t: Out [%0d], expected_y = %0d, actual_y = %0d",
                cyclenum (), n_out, expected_y, actual_y);

      if (expected_y != actual_y) begin
         $display ("Cycle %0d: Test fail: mkForFold 1", cyclenum ());
         $finish;
      end

      if (n_out == fromInteger (n_samples - 1)) begin
         $display ("Cycle %0d: Test ok: mkForFold 1: all %0d outputs ok", cyclenum (), n_samples);
         $finish;
      end
      n_out <= n_out + 1;
   endrule

endmodule: sysForFold_1

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


