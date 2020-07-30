package CycleTest;

import StmtFSM::*;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

function ActionValue#(Bit#(64)) adj_time();
   actionvalue
     let x <- $time();
     if (genVerilog) x = x + 5;     
     return x;
   endactionvalue     
endfunction

(* synthesize *)
module sysCycleTest (Empty);
   
   Reg#(Bit#(8))  count   <- mkReg(0);  
   Reg#(Bit#(16)) partial <- mkReg(0);
   Reg#(Bit#(16)) result  <- mkReg(0);
   
   function RStmt#(Bit#(16)) scaleSeq (Integer scale, Bit#(8) value);
      seq
	 partial <= 0;
	 repeat (fromInteger(scale))
	    action
               partial <= partial + {0,value};
	       $display("(%0d) partial is %0d", adj_time, partial);
	    endaction
	 return partial;
      endseq;
   endfunction

   FSMServer#(Bit#(8), Bit#(16)) scale_serv  <- mkFSMServer(scaleSeq(3));

   let test_seq =  seq
		      $display("(%0d) input   is %0d", adj_time, count);
		      result <- callServer(scale_serv, count);
		      action
			 $display("(%0d) result  is %0d", adj_time, result);
			 count <= count + 1;
		      endaction
		   endseq;
   
   let test_fsm <- mkFSM(test_seq);

   rule start;
      $display("(%0d) starting", adj_time);
      test_fsm.start;
   endrule
   
   rule done (count == 6);
      $finish;
   endrule

      
endmodule


endpackage  
