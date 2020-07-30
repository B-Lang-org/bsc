/* Two or more parStmtFsm inside a while loop. */

import StmtFSM :: *;

(*synthesize*)

module whilePar(Empty);

Reg#(Bit#(4)) i <- mkRegA(0);
Reg#(Bit#(4)) j <- mkRegA(0);
Reg#(Bool) going <- mkRegA(False);
Reg#(int) count <- mkRegA(0);

Stmt test_seq =
    (seq
	    
		while(i < 10)
		seq
		    par
		        action
		            $display("i is %5d", i);
			        i <= i + 1;
			    endaction
		    endpar

		    par
		        action
		            $display("j is %5d", j);
			        j <= j + 1;
		        endaction
	        endpar
			
	    endseq

    endseq);

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
