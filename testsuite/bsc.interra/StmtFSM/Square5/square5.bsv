/* Using break in a repeat loop */

import Vector::*;
import StmtFSM::*;

function ActionValue#(Bit#(64)) adj_time(Bit#(64) dummy);
   actionvalue
     let x <- $time();
     if (genVerilog) x = x + 5;     
     return x;
   endactionvalue     
endfunction

// implement squaring via table lookup
// and RWire hackery

interface Square;
  method Action data_in(Bit#(4) x);
  method Bit#(8) square;
endinterface

(* synthesize, always_ready *)
module mkSquare(Square);

  Vector#(16, Bit#(8)) squares = replicate(?);

  for(Integer i = 0; i < 16; i = i + 1)
    squares[i] = fromInteger(i*i);

  RWire#(Bit#(4)) dataIn <- mkRWire;

  let din = validValue(dataIn.wget);

  method data_in = dataIn.wset;

  method square = select(squares, din);

endmodule

(* synthesize *)
module sysValidValue5(Empty);  
  
  Reg#(Bit#(5)) loop <- mkReg(0);
  
  Square square <- mkSquare;

  Stmt testStmts =
    seq 
       repeat(16)//using repeat
       seq
	  par
	     $display("Square %0d is %0d", loop, square.square);	   
             square.data_in(truncate(loop));
	  endpar
	  loop <= loop + 1;
	  if (loop == 12) break;//using break
       endseq
       $display("Test finished at time %0t", adj_time(0));
    endseq;  

  FSM testFSM <- mkFSM(testStmts);

  Reg#(Bool) started <- mkReg(False);

  rule start(!started);
   testFSM.start;
   started <= True;
  endrule

  rule exit(started && testFSM.done);
   $finish(0);
  endrule

endmodule

