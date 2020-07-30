import Vector::*;
import StmtFSM::*;

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
module sysValidValue(Empty);  
  
  Reg#(Bit#(5)) loop <- mkReg(0);
  
  Square square <- mkSquare;

  // action .. endaction does not work for Bluesim
  // par .. endpar does
  // probably rule/method ordering issue
  Stmt testStmts =
    seq 
      for(loop <= 0; loop < 16; loop <= loop + 1)
         par //action
            $display("Square %0d is %0d", loop, square.square);
            square.data_in(truncate(loop));
         endpar //endaction
      $display("Test finished at time %0t", $time);
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

