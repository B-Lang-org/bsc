/* Using break in nested for loops */

import StmtFSM ::*;

(*synthesize*)
module nestedForLoop1();

Reg#(Bit#(4)) i <- mkRegA(0);
Reg#(Bit#(4)) j <- mkRegA(0);

Stmt test_seq =

  seq
      for (i <= 0 ; i <= 5 ; i <= i + 1)
	      for(j <= 0 ; j <= 5 ; j <= j + 1)
		  seq
			  if ( j == 3) break;
		      $display(" i = %5d   j = %5d", i, j);
		  endseq
 endseq;

mkAutoFSM(test_seq);
endmodule
