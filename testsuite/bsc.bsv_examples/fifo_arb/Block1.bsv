import FIFO::*;
import Includes::*;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

// First version of FIFO arbiter
// no explicit arbitration - compile and see what happens
(* synthesize *)
module mkBlock1( LabIFC );
   Integer fifo_depth = 16;

   // modify data (by adding AA to certain digits)
   // to show it went through the arbiter
   function DataT generate_new_data(DataT val);
      return val + zeroExtend(24'hAA000);
   endfunction

   // create the three fifo instances
   FIFO#(DataT) inbound1();
   mkSizedFIFO#(fifo_depth) the_inbound1(inbound1);

   FIFO#(DataT) inbound2();
   mkSizedFIFO#(fifo_depth) the_inbound2(inbound2);

   FIFO#(DataT) outbound1();
   mkSizedFIFO#(fifo_depth) the_outbound1(outbound1);

   // rule for enqueue of outbound from inbound1
   (* descending_urgency = "enq2, enq1" *)
   rule enq1 (True);
      DataT in_data = inbound1.first;
      DataT out_data = generate_new_data(in_data);
      outbound1.enq(out_data);
      inbound1.deq;
   endrule: enq1

   // rule for enqueue of outbound from inbound2
   rule enq2 (True);
      DataT in_data = inbound2.first;
      DataT out_data = generate_new_data(in_data);
      outbound1.enq(out_data);
      inbound2.deq;
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
