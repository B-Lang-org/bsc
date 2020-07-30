
import FIFO::*;
import GetPut::*;
import Connectable::*;

interface ShiftReg #(type val);
   method Action sin(Maybe#(val) x1);
   method Maybe#(val) sout();
endinterface: ShiftReg

module mkShifter#(Integer sz)(ShiftReg#(val))
   provisos (Bits#(val, bval));

   Reg#(Maybe#(val)) slots[sz];
   
   for (Integer i=0; i<sz; i=i+1)
      begin
	 Reg#(Maybe#(val)) r();
	 mkReg#(Invalid) the_r(r);
	 slots[i] = asReg(r);
      end

   method sout() ;
      let x = slots[sz-1];  
      return (x);
   endmethod: sout

   method sin(v) ;
      action
	 let slotJ = slots[0];
	 
	 for (Integer i=1; i<sz; i=i+1)
	    action
	       let x = slots[i-1];
	       (slots[i]) <= x;
	    endaction
	 (slots[0]) <= v;
      endaction
   endmethod: sin
endmodule: mkShifter


module mkShiftFIFO#(Integer sz)(FIFO#(a))
   provisos (Bits#(a, xs));

   FIFO#(a) fifos[sz];

   for (Integer i = 0; i<sz; i=i+1)
      begin
	 FIFO#(a) fifo();
	 mkFIFO the_fifo(fifo);
	 fifos[i] = fifo;
	 if (i>0)
	    begin
	       let prev = fifos[i-1];
	       mkConnection(fifoToGet(prev),fifoToPut(fifo));
	    end
      end

   let f0 = fifos[0];
   let fn = fifos[sz-1];

   method enq = f0.enq;
   method deq = fn.deq;
   method first = fn.first;
   method Action clear;
      action
	 for (Integer i = 0; i<sz; i=i+1)
	    (fifos[i]).clear;
      endaction
   endmethod
endmodule

