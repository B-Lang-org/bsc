/* Using for loop within a while loop, also calculating no. of clock cycles. */

import StmtFSM ::*;

(*synthesize*)

module forInWhile(Empty);

Reg#(Bit#(4)) i <- mkRegA(0);
Reg#(Bit#(4)) j <- mkRegA(0);
Reg#(Bool) going <- mkRegA(False);
Reg#(int) count <- mkRegA(0);

Stmt test_seq =

    seq
        while ( i <= 5)
		seq  
		    for ( j <= 0 ; j <= 5 ; j <= j + 1)
		    seq
		        $display(" i = %5d   j = %5d", i, j);
				if ( j == 3) break;
		    endseq
		    i <= i + 1;
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
