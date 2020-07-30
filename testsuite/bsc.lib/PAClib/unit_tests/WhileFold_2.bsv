
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
// Test mkWhileFold 2
// Sends 0,1,2,3, ... with every fourth item (3, 7, 11, ...) flagged as "last" item
// The combining function is addition.
// Hence results are sum of each 4-sequence, i.e.,
//     n+(n+1)+(n+2)+(n+3) = 4n+6
// where n = (4 * output index)

(* synthesize *)
module [Module] sysWhileFold_2 (Empty);

   Integer n_samples = 16;

   // ---- Stimulus input: 0,1,2,3, ... with every fourth one paired with "True"

   // Register used to generate inputs
   Reg#(int) count <- mkReg (0);

   FIFOF #(Tuple2 #(int, Bool))  dut_inputs  <- mkPipelineFIFOF;

   rule rl_stimulus;
      if (count == 0) $display ("Cycle %0d: Test start: mkWhileFold 2", cyclenum ());

      Bool sentinel = ((pack (count) & 3) == 3);
      dut_inputs.enq (tuple2 (count, sentinel));
      count <= count + 1;
   endrule

   PipeOut #(Tuple2 #(int, Bool)) po_in = f_FIFOF_to_PipeOut (dut_inputs);

   // ---------------- The dut
   function  int  f_combine (Tuple2 #(int, int) xy);
      match { .x1, .x2 } = xy;
      return (x1 + x2);
   endfunction

   let combine_pipe = mkFn_to_Pipe (f_combine);

   let po_out <- mkWhileFold (combine_pipe, po_in);

   // ---------------- Check outputs

   Reg #(int)  n_out <- mkReg (0);

   rule rl_check;
      let expected_y = 4 * (n_out * 4) + 6;

      let actual_y   = po_out.first (); po_out.deq ();

      $display ("Cycle %0t: Out [%0d], expected_y = %0d, actual_y = %0d",
                cyclenum (), n_out, expected_y, actual_y);

      if (expected_y != actual_y) begin
         $display ("Cycle %0d: Test fail: mkWhileFold 2", cyclenum ());
         $finish;
      end

      if (n_out == fromInteger (n_samples - 1)) begin
         $display ("Cycle %0d: Test ok: mkWhileFold 2: all %0d outputs ok", cyclenum (), n_samples);
         $finish;
      end
      n_out <= n_out + 1;
   endrule

endmodule: sysWhileFold_2

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
