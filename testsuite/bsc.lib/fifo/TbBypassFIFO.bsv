package TbBypassFIFO;

import FIFO::*;
import FIFOF::*;
import SpecialFIFOs::*;

(* synthesize *)
module mkBypassFIFO_int (FIFO#(int));
   FIFOF#(int) f <- mkSizedBypassFIFOF(2);    // 2-element BypassFIFO
   // This adds the notFull and notEmpty as implicit conditions,
   // which is wrong for mkSizedBypassFIFOF, because notEmpty is not
   // the same as RDY_deq (it is not bypassed):
   //return fifofToFifo(f)
   method enq = f.enq;
   method deq = f.deq;
   method first = f.first;
   method clear = f.clear;
endmodule

(* synthesize *)
module mkTbBypassFIFO (Empty);

    FIFO#(int) bfifo <- mkBypassFIFO_int;

    Reg#(int)  cycle <- mkReg (0);
    Reg#(int)  n     <- mkReg (0);

    rule cycles;
       cycle <= cycle + 1;
    endrule

    let x = (cycle & 15);

    // Send, except on 9th-11th cycles (out of 16), to allow FIFO to drain
    rule send ((x < 9) || (x > 11));
        $display ("%d:   enq %d", cycle, n);
        bfifo.enq (n);
        n <= n + 1;
    endrule

    // Receive, except on 1st-3rd cycles (out of 16), to allow FIFO to fill
    rule observe ((x < 1) || (x > 3));
        int x = bfifo.first();
        $display ("%d:       deq %d", cycle, x);
        bfifo.deq();
    endrule

    rule done (n >= 200);
        $display ("%d: Finish", cycle);
        $finish(0);
    endrule

endmodule: mkTbBypassFIFO

endpackage: TbBypassFIFO
