import FIFOF::*;
import StmtFSM::*;

typedef enum { Fill, Drain } State deriving(Eq, Bits);

// force triggering of FIFO enq and deq errors
(* synthesize *)
module sysFIFOErrors(Empty);

 FIFOF#(Bit#(47)) e_fifo2 <- mkUGFIFOF;
 
 FIFOF#(Bit#(47)) e_sizedFIFO <- mkUGSizedFIFOF(3);

 FIFOF#(Bit#(47)) e_fifo1 <- mkUGFIFOF1;
  
 FIFOF#(Bit#(47)) e_lfifo <- mkUGLFIFOF;

 FIFOF#(Bit#(47)) d_fifo2 <- mkUGFIFOF;
 
 FIFOF#(Bit#(47)) d_sizedFIFO <- mkUGSizedFIFOF(3);

 FIFOF#(Bit#(47)) d_fifo1 <- mkUGFIFOF1;
  
 FIFOF#(Bit#(47)) d_lfifo <- mkUGLFIFOF;

 Stmt testStmts = (seq
                      d_fifo2.deq;
                      d_sizedFIFO.deq;
                      d_fifo1.deq;
                      d_lfifo.deq;
                      e_fifo2.enq(0);
                      e_fifo2.enq(0);
                      e_fifo2.enq(0);
                      e_sizedFIFO.enq(0);
                      e_sizedFIFO.enq(0);
                      e_sizedFIFO.enq(0);
                      e_sizedFIFO.enq(0);
                      e_fifo1.enq(0);
                      e_fifo1.enq(0);
                      e_lfifo.enq(0);
                      e_lfifo.enq(0);
                    endseq);

 mkAutoFSM(testStmts);

endmodule



