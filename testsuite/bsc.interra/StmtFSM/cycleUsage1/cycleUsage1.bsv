          /* Cycle usage of FSM constructs: while loop: using seq-endseq */

import StmtFSM ::*;

(*synthesize*)

module cycleUsage1(Empty);

Reg#(Bit#(4)) i <- mkRegA(0);
Reg#(Bit#(6)) count <- mkRegA(0);
Reg#(Bool) going <- mkRegA(False);

Stmt test_seq=
   seq
       while(i < 10)
	       seq
		       $display("Value of i is %5d", i);
			   i <= i + 1;
			   if(i == 5) break;
		   endseq
   endseq;

FSM testFSM <- mkFSM(test_seq);

rule start(!going);
    testFSM.start;
	going <= True;
endrule	

rule always_fire;
	count <= count + 1;
endrule

rule clock_cycles(going && testFSM.done);
     $display("Total number of clock cycles =%5d", count);
	 $finish(0);
endrule	 

endmodule
