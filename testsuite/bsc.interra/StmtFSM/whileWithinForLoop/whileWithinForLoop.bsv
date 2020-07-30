/* Using while loop within for loop */

import StmtFSM ::*;

(*synthesize*)
module whileWithinForLoop();

Reg#(Bit#(4)) i <- mkRegA(0);
Reg#(Bit#(4)) j <- mkRegA(0);

Stmt test_seq =

  seq
      for (i <= 0 ; i <= 5 ; i <= i + 1)
		seq  
		  while ( j <= 5)
		  seq
		      $display(" i = %5d   j = %5d", i, j);
			  j <= j + 1;
		  endseq
		  j <= 0;
		endseq  
 endseq;

mkAutoFSM(test_seq);
endmodule
