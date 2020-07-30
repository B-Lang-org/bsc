/* Using continue in nested repeat loops */

import StmtFSM ::*;

(*synthesize*)
module nestedRepeatLoop1();

Reg#(Bit#(4)) i <- mkRegA(0);
Reg#(Bit#(4)) j <- mkRegA(0);

Stmt test_seq =

  seq
	  repeat(6)
	  seq
		  repeat(6)
		  seq
			  j <= j + 1;
			  if ( j == 3) continue;
		      $display(" i = %5d   j = %5d", i, j);
		  endseq
		  j <= 0;
		  $display("out of the repeat loop i = %5d", i);
		  i <= i + 1;
	  endseq

 endseq;

mkAutoFSM(test_seq);
endmodule
