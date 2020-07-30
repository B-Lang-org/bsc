// Testbench for cross-bar switch XBar.bsv

package Tb;

import List :: *;
import GetPut :: *;
import StmtFSM :: *;

import XBar :: *;

function Bit#(32) destOf (int x);
   return pack (x) & 'hF;
endfunction

(* synthesize *)
module sysTb (Empty);

   // A register to count clock cycles, and a rule to increment it,
   // used in displaying time with inputs and outputs
   Reg#(int) ctr <- mkReg(0);
   rule inc_ctr;
      ctr <= ctr+1;
   endrule

   // Instantiate the DUT (4x4 switch, int packets, lru arbitration)
   // XBar#(int) xbar <- mkXBar (2, destOf, mkMerge2x1_static);
   XBar#(int) xbar <- mkXBar (2, destOf, mkMerge2x1_lru);

   List#(Reg#(int)) xs <- replicateM (4, mkRegU);

   // Rules to dequeue items from each output port
   for (Integer oj = 0; oj < 4; oj = oj + 1) begin
      rule recv;
         let x <- xbar.output_ports[oj].get;
         (xs [oj]) <= x;
         int intoj = fromInteger (oj);
         $display("%d: Out:      (port %1d, val %h)", ctr, intoj, x);
//         $display("%d: Out:      (port %d, val %h)", ctr, intoj, x);

         // ---- Finish when we see sentinel value
         if (x == 'hFFF0) $finish (0);
      endrule
   end

   // This function encapsulates the action of sending a datum x into input port i
   function Action enqueue (Integer i, int x);
      action
         xbar.input_ports[i].put (x);
         int ii = fromInteger (i);
         $display("%d: In:  (port %1d, val %h)", ctr, i, x);
//         $display("%d: In:  (port %d, val %h)", ctr, i, x);
      endaction
   endfunction

   // We define a sequence of actions to exercise the DUT.  (This is a
   // particularly simple example: the feature allows considerably more
   // complicated "programs" than this.)
   Stmt test_seq =
     (seq
         enqueue(0, 'h11);
         enqueue(0, 'h10);
         enqueue(0, 'h12);
         enqueue(0, 'h13);

         enqueue(1, 'h20);
         enqueue(1, 'h23);
         enqueue(1, 'h22);
         enqueue(1, 'h21);

         enqueue(2, 'h30);
         enqueue(2, 'h32);
         enqueue(2, 'h33);
         enqueue(2, 'h31);

         enqueue(3, 'h43);
         enqueue(3, 'h40);
         enqueue(3, 'h42);
         enqueue(3, 'h41);

         action    // no collisions
            enqueue(0, 'h50);
            enqueue(1, 'h51);
            enqueue(2, 'h52);
            enqueue(3, 'h53);
         endaction

         action    // no collisions
            enqueue(0, 'h62);
            enqueue(1, 'h63);
            enqueue(2, 'h60);
            enqueue(3, 'h61);
         endaction

         action    // no collisions
            enqueue(0, 'h71);
            enqueue(1, 'h70);
            enqueue(2, 'h73);
            enqueue(3, 'h72);
         endaction

         action    // collisions
            enqueue(0, 'h81);
            enqueue(1, 'h83);
            enqueue(2, 'h80);
            enqueue(3, 'h82);
         endaction

         // Test arbitration
         action
            enqueue(0, 'h900);
            enqueue(1, 'h910);
         endaction
         action
            enqueue(0, 'ha00);
            enqueue(1, 'ha10);
         endaction
         action
            enqueue(0, 'hb00);
            enqueue(1, 'hb10);
         endaction
         action
            enqueue(0, 'hc00);
            enqueue(1, 'hc10);
         endaction

         // ---- sentinel, to finish simulation
         enqueue (0, 'hFFF0);
      endseq);

   // Next we use this sequence as argument to a module which instantiates a
   // FSM to implement it.
   FSM test_fsm <- mkFSM(test_seq);

   // A register to control the start rule
   Reg#(Bool) going <- mkReg(False);

   // This rule kicks off the test FSM, which then runs to completion.
   rule start (!going);
      going <= True;
      test_fsm.start;
   endrule

endmodule: sysTb

// ================================================================

endpackage: Tb
