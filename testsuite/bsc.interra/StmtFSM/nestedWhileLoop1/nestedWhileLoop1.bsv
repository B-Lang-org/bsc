/* Using continue in nested while loops */

import StmtFSM ::*;

(*synthesize*)
module nestedWhileLoop1();

Reg#(Bit#(4)) i <- mkRegA(0);
Reg#(Bit#(4)) j <- mkRegA(0);

Stmt test_seq =

  seq
	  while ( i <= 5)
		 seq
		     while ( j <= 5)
		     seq
				j <= j + 1;
			   	if ( j == 3) continue;
		        $display(" i = %5d   j = %5d", i, j);
		     endseq
			 j <= 0;
			 $display("out of the while loop i = %5d", i);
			 i <= i + 1;
		 endseq	 
 endseq;

mkAutoFSM(test_seq);
endmodule
