import Clocks::*;
import Gearbox::*;
import StmtFSM::*;

(* synthesize *)
module sysGearboxBubbleTest();
   Reset fastReset <- exposeCurrentReset;
   Clock fastClock <- exposeCurrentClock;
   
   let clkdiv2     <- mkClockDivider(2);
   Clock slow2Clock = clkdiv2.slowClock;
   Reset slow2Reset <- mkAsyncResetFromCR(0, clkdiv2.slowClock);
   
   let clkdiv3   <- mkClockDivider(3);
   Clock slow3Clock = clkdiv3.slowClock;
   Reset slow3Reset <- mkAsyncResetFromCR(0, clkdiv3.slowClock);

   let clkdiv7   <- mkClockDivider(7);
   Clock slow7Clock = clkdiv7.slowClock;
   Reset slow7Reset <- mkAsyncResetFromCR(0, clkdiv7.slowClock);

   let clkdiv19  <- mkClockDivider(19);
   Clock slow19Clock = clkdiv19.slowClock;
   Reset slow19Reset <- mkAsyncResetFromCR(0, clkdiv19.slowClock);
   
   Gearbox#(1,2,Bit#(8))  ftos2 <- mk1toNGearbox(fastClock, fastReset, slow2Clock, slow2Reset);
   Gearbox#(2,1,Bit#(8))  stof2 <- mkNto1Gearbox(slow2Clock, slow2Reset, fastClock, fastReset);
   
   Gearbox#(1,3,Bit#(8))  ftos3 <- mk1toNGearbox(fastClock, fastReset, slow3Clock, slow3Reset);
   Gearbox#(3,1,Bit#(8))  stof3 <- mkNto1Gearbox(slow3Clock, slow3Reset, fastClock, fastReset);
   
   Gearbox#(1,7,Bit#(8))  ftos7 <- mk1toNGearbox(fastClock, fastReset, slow7Clock, slow7Reset);
   Gearbox#(7,1,Bit#(8))  stof7 <- mkNto1Gearbox(slow7Clock, slow7Reset, fastClock, fastReset);
   
   Gearbox#(1,19,Bit#(8))  ftos19 <- mk1toNGearbox(fastClock, fastReset, slow19Clock, slow19Reset);
   Gearbox#(19,1,Bit#(8))  stof19 <- mkNto1Gearbox(slow19Clock, slow19Reset, fastClock, fastReset);

   Reg#(Bit#(10))          bubble_count <- mkReg(0);
   
   Reg#(Bit#(8))           data2  <- mkReg(0);
   Reg#(Bit#(8))           data3  <- mkReg(0);
   Reg#(Bit#(8))           data7  <- mkReg(0);
   Reg#(Bit#(8))           data19  <- mkReg(0);
   Reg#(Bit#(32))          count <- mkReg(0);
   
   Bool canEnqueue2 = (bubble_count[0] == 1);
   Bool canEnqueue3 = (bubble_count[1:0] == 2);
   Bool canEnqueue7 = (bubble_count[2:0] == 5);
   Bool canEnqueue19 = (bubble_count[3:0] == 10);
   
   Bool canDequeue2 = True;
   Bool canDequeue3 = True;
   Bool canDequeue7 = True;
   Bool canDequeue19 = True;
   
   
   rule incr;
      count <= count + 1;
   endrule
   
   rule incr_bubble;
      bubble_count <= bubble_count + 1;
   endrule
   
   rule source_2(canEnqueue2);
      ftos2.enq(unpack(data2));
      data2 <= data2 + 1;
      //$display("[%0t]:02: Enq(%0d)", $time(), data2);
   endrule
   
   rule source_3(canEnqueue3);
      ftos3.enq(unpack(data3));
      data3 <= data3 + 1;
      //$display("[%0t]:03: Enq(%0d)", $time(), data3);
   endrule
   
   rule source_7(canEnqueue7);
      ftos7.enq(unpack(data7));
      data7 <= data7 + 1;
      //$display("[%0t]:07: Enq(%0d)", $time(), data7);
   endrule
   
   rule source_19(canEnqueue19);
      ftos19.enq(unpack(data19));
      data19 <= data19 + 1;
      //$display("[%0t]:19: Enq(%0d)", $time(), data19);
   endrule
   
   rule sink_2(canDequeue2);
      let x = ftos2.first;
      ftos2.deq;
      stof2.enq(x);
      //$display("[%0t]:02: Deq = { %0d, %0d }", $time, x[0], x[1]);
   endrule
   
   rule sink_3(canDequeue3);
      let x = ftos3.first;
      ftos3.deq;
      stof3.enq(x);
      //$display("[%0t]:03: Deq = { %0d, %0d, %0d }", $time, x[0], x[1], x[2]);
   endrule
   
   rule sink_7(canDequeue7);
      let x = ftos7.first;
      ftos7.deq;
      stof7.enq(x);
      //$display("[%0t]:07: Deq = { %0d, %0d, %0d, %0d, %0d, %0d, %0d }", $time, x[0], x[1], x[2], x[3], x[4], x[5], x[6]);
   endrule
   
   rule sink_19(canDequeue19);
      let x = ftos19.first;
      ftos19.deq;
      stof19.enq(x);
      //$display("[%0t]:19: Deq = { %0d, %0d, %0d, %0d, %0d, %0d, %0d, %0d, %0d, %0d, %0d, %0d, %0d, %0d, %0d, %0d, %0d, %0d, %0d }", $time, x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7], x[8], x[9], x[10], x[11], x[12], x[13], x[14], x[15], x[16], x[17], x[18]);
   endrule
   
   rule done_2;
      let x = stof2.first;
      stof2.deq;
      $display("[%0t]:02: Deq = %0d", $time(), x);
   endrule
   
   rule done_3;
      let x = stof3.first;
      stof3.deq;
      $display("[%0t]:03: Deq = %0d", $time(), x);
   endrule
   
   rule done_7;
      let x = stof7.first;
      stof7.deq;
      $display("[%0t]:07: Deq = %0d", $time(), x);
   endrule
   
   rule done_19;
      let x = stof19.first;
      stof19.deq;
      $display("[%0t]:19: Deq = %0d", $time(), x);
   endrule
     
   
   rule simulation_done(count == 1000);
      $display("[%0t] Ending Simualtion", $time());
      $finish(0);
   endrule
   
   
endmodule
