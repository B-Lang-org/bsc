
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
// Test mkMap_with_funnel_indexed

typedef   4  M_t;
typedef   1  K_t;    // should be MK/M

UInt #(M_t) dummy_m = ?;

Bool param_buf_unfunnel = False;

(* synthesize *)
module [Module] sysMap_with_funnel_indexed (Empty);

   Integer n_samples = 8;

   // ---- Stimulus input

   Reg#(int)       j_in          <- mkReg (0);
   FIFOF #(Vec_int) inputs_fifo1  <- mkPipelineFIFOF;
   FIFO  #(Vec_int) inputs_fifo2  <- mkSizedFIFO (32);    // sized to cover latency of dut

   rule rl_stimulus;
      if (j_in == 0) $display ("Cycle %0d: Test start: mkMap_with_funnel_indexed", cyclenum ());

      inputs_fifo1.enq (replicate (j_in));
      inputs_fifo2.enq (replicate (j_in));
      j_in <= j_in + 1;
   endrule

   PipeOut #(Vec_int) po_in = f_FIFOF_to_PipeOut (inputs_fifo1);

   // ---- The dut

   function int bodyfn (Tuple2 #(int, UInt #(LogMK_t))  x_j);
      match { .x, .j } = x_j;
      return x + unpack (extend (pack (j)));
   endfunction

   Pipe #(Tuple2 #(int, UInt #(LogMK_t)), int) bodypipe = mkFn_to_Pipe (bodyfn);

   PipeOut #(Vec_int) po_out <- mkMap_with_funnel_indexed (dummy_m,
                                                           bodypipe,
                                                           param_buf_unfunnel,
                                                           po_in);

   // ---- Gather outputs and check
   Reg #(int) j_out <- mkReg (0);

   rule checkOutput;
      let expected_outs = map (bodyfn,
                               zip (inputs_fifo2.first (),
                                    map (fromInteger, genVector)));
      inputs_fifo2.deq ();

      let actual_outs = po_out.first ();
      po_out.deq ();

      $write ("Cycle %0t: Out [%0d]: ", cyclenum (), j_out);
      display_Vec_int ("  Expected: ", " ", expected_outs, False);
      display_Vec_int ("  Actual:   ", " ", actual_outs,   True);

      if (expected_outs != actual_outs) begin
         $display ("Cycle %0d: Test fail: mkMap_with_funnel_indexed", cyclenum ());
         $finish;
      end

      if (j_out  == fromInteger (n_samples - 1)) begin
         $display ("Cycle %0d: Test ok: mkMap_with_funnel_indexed: all %0d outputs ok", cyclenum (), n_samples);
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
