
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
// Test mkForLoop

(* synthesize *)
module [Module] sysForLoop (Empty);

   Integer n_samples = 16;
   Integer loopbody_latency = 3;    // Simulated pipeline latency through loop body

   // ---- Stimulus input: 0, 1, 2, ...

   // Register used to generate inputs
   Reg#(int) count <- mkReg (0);

   FIFOF #(int)  dut_inputs   <- mkPipelineFIFOF;
   FIFO  #(int)  test_inputs  <- mkSizedFIFO (20); // > latency of dut

   rule rl_stimulus;
      if (count == 0) $display ("Cycle %0d: Test start: mkForLoop", cyclenum ());

      dut_inputs.enq (count);
      test_inputs.enq (count);
      count <= count + 100;
   endrule

   PipeOut #(int) po_in = f_FIFOF_to_PipeOut (dut_inputs);

   // ---------------- The dut
   Integer n = 8;

   function Tuple2 #(int, UInt #(4)) f_loopbody (Tuple2 #(int, UInt #(4)) xj);
      match { .x, .j } = xj;
      return tuple2 (x + 1, j);
   endfunction

   let loopbody_pipe1 = mkFn_to_Pipe (f_loopbody);
   let loopbody_pipe2 = mkBuffer_n (loopbody_latency);
   let loopbody_pipe  = mkCompose (loopbody_pipe1, loopbody_pipe2);

   let po_out <- mkForLoop (n,
                            loopbody_pipe,
                            mkFn_to_Pipe (id),
                            po_in);

   // ---------------- Check outputs

   Reg #(int)  n_out <- mkReg (0);

   rule rl_check;
      let expected_y = test_inputs.first () + fromInteger (n);  test_inputs.deq ();

      let actual_y = po_out.first (); po_out.deq ();

      $display ("Cycle %0t: Out [%0d], expected_y = %0d, actual_y = %0d",
                cyclenum (), n_out, expected_y, actual_y);

      if (expected_y != actual_y) begin
         $display ("Cycle %0d: Test fail: mkForLoop", cyclenum ());
         $finish;
      end

      if (n_out == fromInteger (n_samples - 1)) begin
         $display ("Cycle %0d: Test ok: mkForLoop: All %0d outputs ok", cyclenum (), n_samples);
         $finish;
      end
      n_out <= n_out + 1;
   endrule

endmodule: sysForLoop

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
