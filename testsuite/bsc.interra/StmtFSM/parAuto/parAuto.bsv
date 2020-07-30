/* StmtFSM contains parFsmStmt at its top level and mkAutoFSM created using that stmt. */

import StmtFSM :: *;

(*synthesize*)

module parAuto(Empty);

Reg#(Bit#(4)) i <- mkRegA(0);
Reg#(Bit#(4)) j <- mkRegA(0);

Stmt test_seq =
    par
	    
		while(i < 10)
		    action
		        $display("i is %5d", i);
			    i <= i + 1;
			endaction

		while(j < 10)
		    action
		        $display("j is %5d", j);
			    j <= j + 1;
		    endaction

			
    endpar;

mkAutoFSM(test_seq); 

endmodule
