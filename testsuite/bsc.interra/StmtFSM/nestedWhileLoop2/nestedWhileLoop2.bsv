/* Using break in nested while loops */

import StmtFSM ::*;

(*synthesize*)
module nestedWhileLoop2();

Reg#(Bit#(4)) i <- mkRegA(0);
Reg#(Bit#(4)) j <- mkRegA(0);

Stmt test_seq =

  seq
	  while ( i <= 5)
		 seq
		     while ( j <= 5)
		     seq
		        $display(" i = %5d   j = %5d", i, j);
				j <= j + 1;
			    if ( j == 3) break;
		     endseq
			 j <= 0;
			 $display("out of the while loop i = %5d", i);
			 i <= i + 1;
		 endseq	 
 endseq;

mkAutoFSM(test_seq);
endmodule
