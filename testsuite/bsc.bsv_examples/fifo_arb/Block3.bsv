import FIFO::*;
import FIFOF::*;
import Includes::*;

// Third version of FIFO arbiter
// Applies simple fairness rule
// The FIFO that has waited longest (up to 255 cycles) has priority
// The second FIFO wins in case of a tie

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
(* synthesize *)
module mkBlock3( LabIFC );
   Integer fifo_depth = 16;

  
   // modify data (by adding AA to certain digits)
   // to show it went through the arbiter
   function DataT generate_new_data(DataT val);
      return val + zeroExtend(24'hAA000);
   endfunction

   FIFOF#(DataT) inbound1();
   mkSizedFIFOF#(fifo_depth) the_inbound1(inbound1);
   
   FIFOF#(DataT) inbound2();
   mkSizedFIFOF#(fifo_depth) the_inbound2(inbound2);

   FIFOF#(DataT) outbound1();
   mkSizedFIFOF#(fifo_depth) the_outbound1(outbound1);

   Reg#(Bit#(8)) count1 <- mkReg(0);
   Reg#(Bit#(8)) count2 <- mkReg(0);

   Bool fifo1_hasData = inbound1.notEmpty;
   Bool fifo2_hasData = inbound2.notEmpty;
   Bool both_haveData = fifo1_hasData && fifo2_hasData;

   Bool rule1_can_fire = ((fifo1_hasData && !fifo2_hasData) ||
                          (both_haveData && (count1 > count2)));
                          
   Bool rule2_can_fire = ((fifo2_hasData && !fifo1_hasData) ||
                          (both_haveData && (count1 <= count2)));

   Action inc1 = action
                   if (count1 != 255)
                      count1 <= count1 + 1;
                 endaction;
                  
   Action inc2 = action
                   if (count2 != 255)
                      count2 <= count2 + 1;
                 endaction;

   // increment both counters when nothing happens
   rule idle (!fifo1_hasData && !fifo2_hasData);
      inc1;
      inc2;
   endrule
   
   // rule for enqueue of outbound from inbound1
   rule enq1 (rule1_can_fire);
      DataT in_data = inbound1.first;
      DataT out_data = generate_new_data(in_data);
      outbound1.enq(out_data); 
      inbound1.deq;
      // clear first counter
      count1 <= 0;
      // increment second counter because it is waiting
      inc2; 
   endrule: enq1

   // rule for enqueue of outbound from inbound2
   rule enq2 (rule2_can_fire);
      DataT in_data = inbound2.first;
      DataT out_data = generate_new_data(in_data);
      outbound1.enq(out_data); 
      inbound2.deq;
      // clear second counter
      count2 <= 0;
      // increment first counter because it is waiting
      inc1;
   endrule: enq2

   method Action push1 (DataT a); 
      action
         inbound1.enq(a);
      endaction
   endmethod

   method Action push2 (DataT a);
      action
         inbound2.enq(a);
      endaction
   endmethod
   
   method get(); 
      actionvalue
         outbound1.deq();
         return outbound1.first();
      endactionvalue
   endmethod

endmodule

