
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
// Test mkWhileLoop

(* synthesize *)
module [Module] sysWhileLoop (Empty);

   Integer n_samples = 16;

   // ---- Stimulus input: series of 4-tuples: (x,y), (x,y), ...
   // The (x,y,...) are the "working copies".
   // The (...,x,y) are the original inputs (used for cross-checking results)

   // Registers used to generate numbers to feed to the GCD block
   Reg#(int) count1 <- mkReg (7);
   Reg#(int) count2 <- mkReg (3);

   FIFOF #(Tuple4 #(int, int, int, int))  dut_inputs  <- mkPipelineFIFOF;

   rule rl_stimulus;
      if (count1 == 7) $display ("Cycle %0d: Test start: mkWhileLoop", cyclenum ());

      let next_input = tuple4 (count1, count2, count1, count2);
      dut_inputs.enq (next_input);
      count1 <= count1 + 3;
      count2 <= count2 + 2;
   endrule

   PipeOut #(Tuple4 #(int, int, int, int)) po_in = f_FIFOF_to_PipeOut (dut_inputs);

   // ---------------- The dut
   function Tuple2 #(Tuple4 #(int, int, int, int), Bool) f_preTest (Tuple4 #(int, int, int, int) xyxy);
      match { .x, .y, .xorig, .yorig } = xyxy;
      return tuple2 (tuple4 (x, y, xorig, yorig), (y != 0));
   endfunction

   function Tuple4 #(int, int, int, int) f_postTest (Tuple4 #(int, int, int, int) xyxy);
      match { .x, .y, .xorig, .yorig } = xyxy;
      return ( (x > y) ? tuple4 (y, x, xorig, yorig) : tuple4 (x, y - x, xorig, yorig) );
   endfunction

   function Tuple3 #(int, int, int) f_final (Tuple4 #(int, int, int, int) xyxy);
      match { .x, .y, .xorig, .yorig } = xyxy;
      return tuple3 (x, xorig, yorig);
   endfunction

   // ---- Note: the buffering below for the preTest is not functionally necessary.
   // We add the buffer just to increase loop occupancy, which allows the loop
   // to deliver outputs out of order.

   let po_out <- mkWhileLoop (mkFn_to_Pipe_Buffered (False, f_preTest, True),
                              mkFn_to_Pipe (f_postTest),
                              mkFn_to_Pipe (f_final),
                              po_in);

   // ---------------- Check outputs
   // Each output is (result, x, y).  Check that GCD (x,y) = result

   Reg #(int)  n_out <- mkReg (0);
   Reg #(int)  x     <- mkRegU;
   Reg #(int)  y     <- mkReg (0);
   Reg #(Bool) busy  <- mkReg (False);

   rule rl_start (! busy);
      match { .g, .xorig, .yorig } = po_out.first ();
      x <= xorig;
      y <= yorig;
      busy <= True;
   endrule

   rule rl_swap (busy && (x > y) && (y != 0));
      x <= y; y <= x;
   endrule

   rule rl_sub (busy && (x <= y) && (y != 0));
      y <= y - x;
   endrule

   rule rl_check (busy && (y == 0));
      match { .g, .xorig, .yorig } = po_out.first ();
      po_out.deq ();

      $display ("Cycle %0t: Out [%0d], x = %0d, y = %0d, expected %0d, actual %0d",
                cyclenum (), n_out, xorig, yorig, x, g);

      if (g != x) begin
         $display ("Cycle %0d: Test fail: mkWhileLoop", cyclenum ());
         $finish;
      end

      if (n_out == fromInteger (n_samples - 1)) begin
         $display ("Cycle %0d: Test ok: mkWhileLoop: all %0d outputs ok", cyclenum (), n_samples);
         $finish;
      end
      n_out <= n_out + 1;
      busy <= False;
   endrule

endmodule: sysWhileLoop

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
