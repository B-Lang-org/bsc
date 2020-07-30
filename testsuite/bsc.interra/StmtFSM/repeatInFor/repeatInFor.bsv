/* Using repeat loop inside a for loop, also calculating the timing. */

import StmtFSM ::*;

(*synthesize*)

module repeatInFor(Empty);

Reg#(Bit#(4)) i <- mkRegA(0);
Reg#(Bit#(3)) j <- mkRegA(0);
Reg#(Bool) going <- mkRegA(False);
Reg#(int)  count <- mkRegA(0);

Stmt test_seq=
    seq
        
		for(i <= 0; i < 5; i <= i + 1)
	    
		seq    
			repeat(6)
		        
				seq
			        j <= j + 1;
				    if ( j == 3) continue;
				    $display("i is %5d & j is %5d", i , j);
				endseq
				
				j <= 0;
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

