/* Using repeat loop within a while loop, also calculating no. of clock cycles. */

import StmtFSM ::*;

(*synthesize*)

module repeatInWhile(Empty);

Reg#(Bit#(4)) i <- mkRegA(0);
Reg#(Bit#(4)) j <- mkRegA(0);
Reg#(Bool) going <- mkRegA(False);
Reg#(int) count <- mkRegA(0);

Stmt test_seq =

    seq
        
		while (i <= 5)
		
		seq  
		    repeat(6)
		    
			seq
				j <= j + 1;
				if ( j == 3 || j == 4) continue;
		        $display(" i = %5d   j = %5d", i, j);
		    endseq
		    
			j <= 0;
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
