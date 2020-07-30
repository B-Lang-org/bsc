package DQueueTb;

import QType::*;
import DQueueConfig::*;
import DQueue::*;
import Priority::*;
import StmtFSM::*;

// This is a rudimentary testbench for the priority queue design.  It is a
// module synthesizable to RTL; it communicates only via $display, so its
// interface to the external world is Empty.

(* synthesize *)
module sysDQueueTb(Empty);
   // A register to count clock cycles, and a rule to increment it.
   Reg#(int) ctr <- mkReg(0);
   rule inc_ctr;
      ctr <= ctr+1;
   endrule

   // Instantiate the DUT.
   let queue <- mkQueue;

   // Two functions to define the actions of enqueueing and dequeueing items.
   // The first of these sets only a few fields -- those on which the ordering
   // is based, and one more to break ambiguity.
   function Action enqueue(Priority#(PRIORITY_SIZE) p, Bit#(RW_SIZE) r, Bit#(SOURCE_ID_SIZE) s);
      action
	 Entry e = empty_entry;
	 e.prio = p; e.command_type.rw = r; e.source_id = s;
	 queue.enq(e);
	 $display("%d: In:  (%d, %d, %d)", ctr, priority2uint(p), r, s);
      endaction
   endfunction

   function Action dequeue();
      action
	 let e = queue.first;
	 queue.deq;
	 $display("%d: Out: (%d, %d, %d)", ctr, priority2uint(e.prio), e.command_type.rw, e.source_id);
      endaction
   endfunction

   // We define a sequence of actions to exercise the DUT.  (This is a
   // particularly simple example: the feature allows considerably more
   // complicated "programs" than this.)
   Stmt test_seq =
     (seq
         enqueue(7,0,0);
	 enqueue(3,1,1);
	 par dequeue; enqueue(2,0,3); endpar
	    // these may happen on the same cycle, but may instead be "interleaved"
	 enqueue(6,1,4);
	 enqueue(6,1,5);
	    // the queue is now full.
	 par dequeue; enqueue(2,0,6); endpar
            // accordingly, the above actions cannot be simultaneous.
	 dequeue;
	 dequeue;
	 dequeue;
	 dequeue;
	 par dequeue; enqueue(2,0,7); endpar
	 enqueue(6,1,99);
	 //queue.clear;
      endseq);
   
   // Next we use this sequence as argument to a module which instantiates a
   // FSM to implement it.
   FSM test_fsm <- mkFSM(test_seq);

   // A register to control the following two rules:
   Reg#(Bool) going <- mkReg(False);

   // This rule starts the test FSM.
   rule start (!going);
      going <= True;
      test_fsm.start;
   endrule
   
   // This rule fires when the FSM has finished its work, and stops the
   // simulation. 
   rule stop (going && test_fsm.done);
      $finish(0);
   endrule
endmodule

endpackage
