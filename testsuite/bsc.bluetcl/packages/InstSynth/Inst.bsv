import FIFO :: * ;
import FIFOLevel :: *;
import Inst_auto :: * ;

(* synthesize *)
module sysInst ();
   
   FIFO#(int) xxx <- sysInst2 ;
   
   FIFO#(int)      fifo_1 <- mkFIFO_Synth;
   FIFO#(Int#(32)) fifo_2 <- mkFIFO_Synth;
   FIFO#(Bit#(32)) fifo_3 <- mkFIFO_Synth;

   FIFOCountIfc#(int,10)  lf1 <- mkFIFOCount_Synth ;
   FIFOCountIfc#(int,11)  lf2 <- mkFIFOCount_Synth ;
   FIFOCountIfc#(int,12)  lf3 <- mkFIFOCount_Synth ;
   FIFOCountIfc#(Bool,10) lf4 <- mkFIFOCount_Synth ;
   
   
endmodule


module sysInst2 ( FIFO#(x) )
   provisos ( MakeInst_mkFIFO #(  FIFO::FIFO#(x) ) 
             ,MakeInst_mkFIFOCount #( FIFOLevel::FIFOCountIfc#(x, 10))
             );

   FIFO#(int)      fifo_1 <- mkFIFO_Synth;
   FIFO#(x)        fifo_2 <- mkFIFO_Synth;
   FIFO#(Bit#(32)) fifo_3 <- mkFIFO_Synth;

   FIFOCountIfc#(x,10)    lf1 <- mkFIFOCount_Synth ;
   FIFOCountIfc#(int,11)  lf2 <- mkFIFOCount_Synth ;
   FIFOCountIfc#(int,12)  lf3 <- mkFIFOCount_Synth ;
   FIFOCountIfc#(Bool,10) lf4 <- mkFIFOCount_Synth ;
   
   return fifo_2 ;
   
endmodule
