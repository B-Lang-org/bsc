
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
// Test mkFork and mkJoin

(* synthesize *)
module [Module] sysfork_join (Empty);

   Integer n_samples = 10;

   // ---- Stimulus input: series of 32b values
   // ---- Lower 16b = 10,12,14, ...
   // ---- Upper 16b = 20,23,26, ...
   Reg #(Bit #(16))    l_in_r      <- mkReg (10);
   Reg #(Bit #(16))    u_in_r      <- mkReg (20);
   FIFOF #(Bit #(32))  dut_inputs  <- mkPipelineFIFOF;
   FIFO  #(Bit #(32))  test_inputs <- mkSizedFIFO (10); // >= latency of dut

   rule rl_stimulus;
      if (l_in_r == 10) $display ("Cycle %0d: Test start: mkFork mkJoin", cyclenum ());

      let next_input = { u_in_r, l_in_r };
      dut_inputs.enq (next_input);
      test_inputs.enq (next_input);
      l_in_r <= l_in_r + 2;
      u_in_r <= u_in_r + 3;
   endrule

   PipeOut #(Bit #(32)) po_in = f_FIFOF_to_PipeOut (dut_inputs);

   // ---------------- The dut (fork, transform_each_arm, join)
   // ---- Fork
   function Tuple2 #(Bit #(16), Bit #(16))  fork_fn (Bit #(32) ul);
      return tuple2 (ul[31:16], ul[15:0]);
   endfunction

   match { .pou1, .pol1 } <- mkFork (fork_fn, po_in);

   // ---- Transform each arm
   let pou2 <- mkFn_to_Pipe (f_incr_by (7), pou1);
   let pol2 <- mkFn_to_Pipe (f_incr_by (3), pol1);

   // ---- Join
   function Tuple2 #(Bit #(16), Bit #(16)) join_fn (Bit #(16) vu, Bit #(16) vl);
      return ( tuple2 (vl, vu) );    // swaps upper and lower
   endfunction

   let po_out <- mkJoin (join_fn, pou2, pol2);

   // ---- Collect output and check
   Reg #(int) j_out <- mkReg (0);

   rule checkOutput;
      let v_in = test_inputs.first (); test_inputs.deq ();
      let expected_u = f_incr_by (3, v_in [15:0]);
      let expected_l = f_incr_by (7, v_in [31:16]);

      match { .actual_u, .actual_l } = po_out.first ();  po_out.deq ();

      $display ("Cycle %0t: Out [%0d]: expected (%0d, %0d), actual (%0d, %0d)",
                cyclenum (), j_out, expected_u, expected_l, actual_u, actual_l);

      if ((expected_u != actual_u) || (expected_l != actual_l)) begin
         $display ("Cycle %0d: Test fail: mkFork mkJoin", cyclenum ());
         $finish;
      end

      if (j_out  == fromInteger (n_samples - 1)) begin
         $display ("Cycle %0d: Test ok: mkFork mkJoin: all %0d outputs ok", cyclenum (), n_samples);
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
