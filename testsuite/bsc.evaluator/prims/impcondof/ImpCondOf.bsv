import FIFO::*;
import StmtFSM::*;

(* synthesize *)
module sysImpCondOf(Empty);

   FIFO#(void) f <- mkFIFO;

   Bool enq_ready = impCondOf(f.enq);
   Bool deq_ready = impCondOf(f.deq);

   rule display_readys;
      $display("Enq ready: %0b Deq ready: %0b Time: %0t",
	       enq_ready, deq_ready, $time);
   endrule

   Stmt test_prog =
   (seq
       action
         f.enq(?);
         $display ("Enq one item at time %0t", $time);
       endaction
       action
         f.enq(?);
         $display ("Enq another item at time %0t", $time);
       endaction
       $display ("Wait at time %0t", $time);
       action
         f.deq;
         $display ("Deq at time %0t", $time);
       endaction
       action
         f.deq;
         $display ("Deq at time %0t", $time);
       endaction
       $display ("Wait at time %0t", $time);
       $display("Testbench finished at time %0t", $time);
    endseq);

   FSM test_fsm <- mkFSM(test_prog);

   Reg#(Bool) started <- mkReg(False);

   rule start(!started);
      started <= True;
      test_fsm.start;
   endrule

   rule exit(started && test_fsm.done);
     $finish(0);
   endrule

endmodule
