package ServerInServer;

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
module sysServerInServer (Empty);
   
   Reg#(Bit#(8))  count   <- mkReg(0);  
   Reg#(Bit#(32)) partial <- mkReg(0);
   Reg#(Bit#(32)) result  <- mkReg(0);
   
   function RStmt#(Bit#(32)) squareSeq (Bit#(32) value);
      seq
	 actionvalue
	    return value * value;
	 endactionvalue
      endseq;
   endfunction

   FSMServer#(Bit#(32), Bit#(32)) square_serv <- mkFSMServer(squareSeq);

   function RStmt#(Bit#(32)) powerSeq (Integer power, Bit#(8) value);
      seq
	 partial <= {0, value};
	 repeat (fromInteger(power))
	    seq
	       partial <- callServer(square_serv, partial);
	    endseq
	 return partial;
      endseq;
   endfunction
   
   // calculates n^8
   FSMServer#(Bit#(8), Bit#(32)) power_serv  <- mkFSMServer(powerSeq(3));

   let test_seq =  seq
		      $display("(%0d) input   is %0d", adj_time, count);
		      result <- callServer(power_serv, count);
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
