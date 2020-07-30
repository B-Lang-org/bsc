                /* Usage of clear method of Once Interface */

import StmtFSM ::*;

(*synthesize*)

module clearOfOnce(Empty);

Reg#(Bit#(4)) i <- mkRegA(0);
Reg#(Bit#(3)) j <- mkRegA(0);
Reg#(Bit#(6)) count <- mkRegA(0);

Stmt test_seq=
    seq
        
		for(i <= 0; i < 8; i <= i + 1)
	    
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


FSM pfsm <- mkFSM(test_seq);
Once fsmOnce <- mkOnce(pfsm.start);

Reg#(Bit#(2)) going <- mkRegA(0);

rule shot(going == 0);
    fsmOnce.start;
	going <= 2'b01;
endrule

rule clear((going == 2'b01)&& fsmOnce.done && pfsm.done);
    fsmOnce.clear;
	$display("The clear method of Once is called, FSM can be started again.");
	going <= 2'b10;
endrule	

rule restart(going == 2'b10);
    $display("Restarting the FSM ..... ");
	fsmOnce.start;
	going <= 2'b11;
endrule	

rule exit((going == 2'b11) && fsmOnce.done && pfsm.done);
	$finish(0);
endrule	

endmodule
