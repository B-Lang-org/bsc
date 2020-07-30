import StmtFSM ::*;

(*synthesize*)

module forTest();

Reg#(Bit#(4)) i <- mkRegA(0);

Stmt test_seq=
 seq
	
	for ( i <= 1; i <= 10; i <= i + 1)
	seq
		 //i <= i + 1;
		 $display("i is %d", i);
		 if (i == 4) continue;
		 $display("After continue");
	endseq
	
 endseq;

mkAutoFSM(test_seq);

endmodule    
