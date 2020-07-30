package RepeatTest;

import StmtFSM::*;

(* synthesize *)
module mkRepeatTest (Empty);
   
   Reg#(Bit#(8)) count <- mkReg(0);
   Reg#(Bit#(8)) i <- mkReg(0);

   Stmt test_seq =  seq
		       $display("(%5d) Start 1.", $time);
		       $display("(%5d) Start 2.", $time);
		       repeat (7)
			  seq
			     count <= count + 1;
			     $display("(%5d) %d A", $time, count);
			  endseq
		       repeat (20)
			  seq
			     count <= count + 1;
			     $display("(%5d) %d A", $time, count);
			     if (count == 10) break;
			  endseq
		       $display("(%5d) %d C", $time, count);
		       $display("(%5d) %d D", $time, count);
		    endseq;
   
   let test_fsm <- mkAutoFSM(test_seq);
   
endmodule


endpackage  
