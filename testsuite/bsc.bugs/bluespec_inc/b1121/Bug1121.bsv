import StmtFSM ::*;
import FIFO ::*;

(*synthesize*)
module testSizedFIFO();

FIFO#(Bit#(16)) dut <- mkSizedFIFO(5);

Reg#(Bit#(4)) i <- mkRegA(0);
Reg#(Bit#(4)) j <- mkRegA(0);

Stmt driverMonitors =
 (seq
    dut.clear;

    par
      for(i <= 1; i <= 10; i <= i + 1)
      seq
          dut.enq({0, i});
          $display("Enqueue %d", i);
      endseq

      seq
          while(i < 5)
          seq
             noAction;
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
    test.start;
    going <= True;
endrule

endmodule
