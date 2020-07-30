// testbench that checks the depth of explicitly sized FIFOs
// since it uses the FIFO rather than the FIFOF interface
// it only checks that you can enqueue up to the depth parameter,
// rather than also checking that the FIFO is full at that point

import FIFO::*;
import BSVFIFO::*;
import List::*;

interface Done;
  method Bool done();
  method Bit#(32) count();
endinterface

// dynamically select a list element by index
// return Invalid if the element is not found
function Maybe#(a) selectM(List#(a) l, b k) provisos(Eq#(b), Literal#(b));
  function f(Tuple2#(a,b) p, Maybe#(a) r);
    return ((k == fromInteger(tpl_2(p))) ? (Valid (tpl_1(p))) : r);
  endfunction
    return foldr(f,Invalid,zip(l,upto(0,length(l))));
endfunction

module mkSizedFIFOTest#(Integer fifosize)(Done);
  FIFO#(Bit#(32)) fifo();
  mkSizedBSVFIFO#(fifosize) i_fifo(fifo);

  // count the number of elements enqueued
  Reg#(Bit#(32)) counter();
  mkReg#(0) i_counter(counter);

  rule enq (counter < fromInteger(fifosize));
    fifo.enq(0);
    $display("FIFO %0d count %0d", fifosize, counter);
    counter <= counter + 1; 
  endrule

  method done();
    return (counter >= fromInteger(fifosize));
  endmethod

  method count();
    return (counter);
  endmethod

endmodule

// constants controlling the sizes of FIFOs to test
Integer startSize = 1;
Integer maxSize   = 12;

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
       // fell off the edge of the tester list!
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
