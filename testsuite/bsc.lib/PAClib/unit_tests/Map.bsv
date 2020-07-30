
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
// Test mkMap

(* synthesize *)
module [Module] sysMap (Empty);

   Integer n_samples = 8;

   // ---- Stimulus input: Vectors of all 0, all 1, all 2, ...

   Reg#(int)       j_in          <- mkReg (0);
   FIFOF #(Vec_int) inputs_fifo1  <- mkPipelineFIFOF;
   FIFO  #(Vec_int) inputs_fifo2  <- mkSizedFIFO (32);    // depth >= latency of dut

   rule rl_stimulus;
      if (j_in == 0) $display ("Cycle %0d: Test start: mkMap", cyclenum ());

      inputs_fifo1.enq (replicate (j_in));
      inputs_fifo2.enq (replicate (j_in));
      j_in <= j_in + 1;
   endrule

   PipeOut #(Vec_int) po_in = f_FIFOF_to_PipeOut (inputs_fifo1);

   // ---- The dut

   Pipe #(int, int) bodypipe = mkFn_to_Pipe (f_incr_by (10));

   PipeOut #(Vec_int) po_out <- mkMap (bodypipe, po_in);

   // ---- Gather outputs and check
   Reg #(int) j_out <- mkReg (0);

   rule checkOutput;
      let expected_outs = map (f_incr_by (10), inputs_fifo2.first ());
      inputs_fifo2.deq ();

      let actual_outs = po_out.first ();
      po_out.deq ();

      $write ("Cycle %0t: Out [%0d]: ", cyclenum (), j_out);
      display_Vec_int ("  Expected: ", " ", expected_outs, False);
      display_Vec_int ("  Actual:   ", " ", actual_outs,   True);

      if (expected_outs != actual_outs) begin
         $display ("Cycle %0d: Test fail: mkMap", cyclenum ());
         $finish;
      end

      if (j_out  == fromInteger (n_samples - 1)) begin
         $display ("Cycle %0d: Test ok: mkMap: all %0d outputs ok", cyclenum (), n_samples);
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
