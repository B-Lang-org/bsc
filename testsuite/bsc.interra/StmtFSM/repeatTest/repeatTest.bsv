/* Using break and continue in a seq-endseq where repeat is used */

import StmtFSM ::*;

function ActionValue#(Bit#(64)) adj_time(Bit#(64) dummy);
   actionvalue
     let x <- $time();
     if (genVerilog) x = x + 5;     
     return x;
   endactionvalue     
endfunction

(* synthesize *)
module repeatTest (Empty);
   
   Reg#(Bit#(8)) count <- mkReg(0);
   Reg#(Bit#(8)) i <- mkReg(0);

   Stmt test_seq =  
       seq
               $display("(%5d) Start 1.", adj_time(0));
               $display("(%5d) Start 2.", adj_time(0));
               
			  repeat (7)
                seq
                   count <= count + 1;
				   if (count == 5 ) continue;
                   $display("(%5d) %d A", adj_time(0), count);
                endseq
               
			  repeat (20)
                seq
                   count <= count + 1;
                   $display("(%5d) %d A", adj_time(0), count);
                   if (count == 10) break;
                endseq
               
			   $display("(%5d) %d C", adj_time(0), count);
               $display("(%5d) %d D", adj_time(0), count);
           
		 endseq;
   
mkAutoFSM(test_seq);
   
endmodule
