/* check that sized FIFO has the right depth between C and Verilog */

import FIFOF::*;
import List::*;

interface Done;
  method Bool done();
  method Bit#(32) count();
endinterface

module mkSizedFIFOTest#(Integer fifosize)(Done);
  FIFOF#(Bit#(32)) fifo();
  mkSizedFIFOF#(fifosize) i_fifo(fifo);
  // check 0 size fifo too
  FIFOF#(PrimUnit) fifo0();
  mkSizedFIFOF#(fifosize) i_fifo0(fifo0);
  Reg#(Bit#(32)) counter();
  mkReg#(0) i_counter(counter);

  rule enq (counter < fromInteger(fifosize));
    fifo.enq(0);
    fifo0.enq(PrimUnit {});
    $display("FIFO %0d count %0d", fifosize, counter);
    counter <= counter + 1; // count the number of things enqueued
  endrule

  method done();
    return (counter >= fromInteger(fifosize) && !(fifo.notFull) && !(fifo0.notFull));
  endmethod

  method count();
    return (counter);
  endmethod

endmodule

Integer startSize = 1;
Integer maxSize   = 32;

(* synthesize *)
module sysSizedFIFOTest(Empty);

  List#(Integer) testSizes = upto(startSize,maxSize);
  List#(Done) testers <- mapM(mkSizedFIFOTest, testSizes);
  
  Reg#(Bit#(32)) count();
  mkReg#(0) i_count(count);
  // need to wait until the nth cycle is over
  rule test(count <= fromInteger(maxSize) && 
            count >= fromInteger(startSize));

    // indexing by list position not FIFO size
    Maybe#(Done) dut = selectM(testers, (count - fromInteger(startSize)));
    case (dut) matches
       Invalid : action 
                    $display("Fail %0d", count); 
                    $finish(0); 
                  endaction
       tagged Valid .done_ifc : if (done_ifc.done)
                                 $display("Pass %0d", count);
                               else
                                 action $display("Fail %0d %0d", 
                                                 count, 
                                                 done_ifc.count); 
                                        $finish(0);
                                 endaction
    endcase  
  endrule

  rule step (True);
    if (count > fromInteger(maxSize))
       $finish(0);
    else
       count <= count + 1;
  endrule 

endmodule
