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
// Test mkSource_from_fav, mkFn_to_Pipe_SynchBuffered, mkSynchBuffer, mkSink_to_fa

(* synthesize *)
module [Module] sysSynchPipe (Empty);

   Integer n_samples = 8;

   Reg #(int) x <- mkReg (2);

   function ActionValue #(int) next_int ();
      actionvalue
         x <= x + 1;
         return x;
      endactionvalue
   endfunction

   PipeOut #(int) po1 <- mkSource_from_fav (next_int);

   function int square (int y) = y * y;

   PipeOut #(int) po2 <- mkFn_to_Pipe_SynchBuffered (tagged Valid (1), square, tagged Valid (0), po1);

   Reg #(int) xx <- mkReg (0);

   function Action showint (int z);
      action
         $display ("%0t: sinking %0d", cyclenum(), z);

         if ((xx * xx) != z) begin
            $display ("Cycle %0d: Test fail: mkTestSynchPipe", cyclenum ());
            $finish;
         end

         if (xx  == fromInteger (n_samples - 1)) begin
            $display ("Cycle %0d: Test ok: mkTestSynchPipe: all %0d outputs ok", cyclenum (), n_samples);
            $finish;
         end

         xx <= xx + 1;
      endaction
   endfunction

   let emptyifc <- mkSink_to_fa (showint, po2);

   return emptyifc;
endmodule

