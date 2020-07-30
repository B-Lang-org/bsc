import FIFO::*;

typedef enum { Fill, Drain } State deriving(Eq, Bits);

// poke and prod FIFOs to test vcd dumping
// goal is to trigger the full range of dynamic situations
// filling, pausing, draining, etc.
module sysMoreFIFOTest(Empty);

 Reg#(Bit#(47)) newElement <- mkReg(47'h7baddeadbeef);

 Reg#(Bit#(7)) topCount <- mkReg(0);

 // topCount5 == 4 triggers a post-fill pause
 Reg#(Bit#(3)) topCount5 <- mkReg(0);

 // topCount7 == 3 triggers a post-drain pause
 Reg#(Bit#(3)) topCount7 <- mkReg(0);

 Reg#(Bit#(7)) curCount <- mkReg(0);

 Reg#(State) state <- mkReg(Fill);

 // when True, we are pausing
 Reg#(Bool) pauseToggle <- mkReg(False);

 FIFO#(Bit#(47)) fifo2 <- mkFIFO;
 
 FIFO#(Bit#(47)) sizedFIFO <- mkSizedFIFO(23);

 FIFO#(Bit#(47)) fifo1 <- mkFIFO1;
  
 FIFO#(Bit#(47)) lfifo <- mkLFIFO;

 Action plusTopCount = action
                              
                         if(topCount == 20) $finish(0);
               
                         topCount <= topCount + 1;

                         if(topCount5 < 5)
                           topCount5 <= topCount5 + 1;
                         else
                           topCount5 <= 0;

                         if(topCount7 < 7)
                           topCount7 <= topCount7 + 1;
                         else
                           topCount7 <= 0;

                       endaction;

 // all other behavior is blocked by pauseToggle, so unblock it                      
 rule unpause(pauseToggle);
   pauseToggle <= False;
 endrule

 rule donefill(curCount == topCount && state == Fill && !pauseToggle);

   // advance state
   state <= Drain;

   // trigger pause
   if (topCount5 == 4) pauseToggle <= True;
             
 endrule

 rule donedrain(curCount == 0 && state == Drain && !pauseToggle);
   
   // advance state
   state <= Fill;
     
   plusTopCount;

   // trigger pause
   if (topCount7 == 3) pauseToggle <= True;

 endrule

 rule fill_fifo2(state == Fill && curCount < topCount && !pauseToggle);
   $display("Enq %0h into fifo2 at time %0t", newElement, $time);
   fifo2.enq(newElement);
 endrule

 rule drain_fifo2(state == Drain && curCount > 0 && !pauseToggle);
   $display("Deq %0h from fifo2 at time %0t", fifo2.first, $time);
   fifo2.deq;
 endrule

 rule fill_sizedFIFO(state == Fill && curCount < topCount && !pauseToggle);
   $display("Enq %0h into sizedFIFO at time %0t", newElement, $time);
   sizedFIFO.enq(newElement);
 endrule

 rule drain_sizedFIFO(state == Drain && curCount > 0 && !pauseToggle);
   $display("Deq %0h from sizedFIFO at time %0t", sizedFIFO.first, $time); 
   sizedFIFO.deq;
 endrule

 rule fill_fifo1(state == Fill && curCount < topCount && !pauseToggle);
   $display("Enq %0h into fifo1 at time %0t", newElement, $time);
   fifo1.enq(newElement);
 endrule

 rule drain_fifo1(state == Drain && curCount > 0 && !pauseToggle);
   $display("Deq %0h from fifo1 at time %0t", fifo1.first, $time);
   fifo1.deq;
 endrule

 rule fill_lfifo(state == Fill && curCount < topCount && !pauseToggle);
   $display("Enq %0h into lfifo at time %0t", newElement, $time);
   lfifo.enq(newElement);
 endrule

 rule drain_lfifo(state == Drain && curCount > 0 && !pauseToggle);
   $display("Deq %0h from lfifo at time %0t", lfifo.first, $time);
   lfifo.deq;
 endrule
 
 rule trackfill(state == Fill && curCount < topCount && !pauseToggle);
   curCount <= curCount + 1;
   newElement <= newElement + 7;

   if(curCount[0] == 0) pauseToggle <= True;

 endrule

 rule trackdrain(state == Drain && curCount > 0 && !pauseToggle);
   curCount <= curCount - 1;
   
   if(curCount[1:0] == 0) pauseToggle <= True;
 endrule

endmodule



