/* Using for loop and continue in a par-endpar context */

import StmtFSM ::*;
import FIFO ::*;

(*synthesize*)
module fifoTest();

FIFO#(Bit#(16)) dut <- mkSizedFIFO(5);

Reg#(Bit#(4)) i <- mkRegA(0);

Stmt driverMonitors =
 (seq
    dut.clear;

    par
       for(i <= 0; i <= 11; i <= i + 1)
       seq
          dut.enq({0, i});
          $display("Enqueue %d", i);
       endseq
        
       seq
          while(i < 5)
          seq
			 continue;
          endseq
          while(i <= 10)
		 action
             dut.deq;
             $display("Value read %d", dut.first);
         endaction
    endseq

  endpar
  
  $finish(0);
  
 endseq);

FSM test <- mkFSM(driverMonitors);

Reg#(Bool) going <- mkReg(False);

rule start(!going);
    going <= True;
    test.start;
endrule

endmodule
