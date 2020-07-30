/*----------------------------------------------------------------------------

FindFIFOM2
 
This version of the find FIFO returns more than just a Bool.
It also returns data.  This can be used to bypass values.

-----------------------------------------------------------------------------*/

import ConfigReg::*;

interface FindFIFOM#(type t1, type t2);
   method Action enq(t1 x);
   method Action deq();
   method t1     first();
   method Action clear();
   method Maybe#(t2) find(function Maybe#(t2) f(t1 x));
   method Bool   notEmpty();
endinterface

module mkFindFIFOM (FindFIFOM#(t1,t2)) provisos (Bits#(t1,szt1));

   Reg#(Maybe#(t1)) data();
   mkReg#(Invalid) data_r(data);

   RWire#(void) deq_probe();
   mkRWire deq_probe_r(deq_probe);

   RWire#(t1) enq_probe();
   mkRWire enq_probe_r(enq_probe);

   RWire#(void) clr_probe();
   mkRWire clr_probe_r(clr_probe);

   Bool is_deq = isValid(deq_probe.wget);
   Bool is_enq = isValid(enq_probe.wget);
   Bool is_clr = isValid(clr_probe.wget);
   
   Bool has_data = isValid(data);
   Bool can_enq = is_deq || !has_data;
   Bool can_deq = has_data;

   (* fire_when_enabled, no_implicit_conditions *)
   rule handle_inputs;
      if (is_clr)
	 data <= Invalid;
      else
	 if (is_enq)
	    data <= enq_probe.wget;
	 else
	    if (is_deq)
	       data <= Invalid;
	    else
	       data <= data;
   endrule
   
   method enq(x) if (can_enq) = enq_probe.wset(x);
   method deq() if (can_deq) = deq_probe.wset(?);
   method clear() = clr_probe.wset(?);
   
   method first() if (has_data) = validValue(data);

   method find(f) = has_data ? f(validValue(data)) : Invalid;
   method notEmpty() = has_data;

endmodule



/*----------------------------------------------------------------------------

mkFindFIFOBypassM
 
This version of the find FIFO is the same as FindFIFOM2, except
that it can bypass values directly from the enqueue method, rather
than waiting a cycle for the enqueued value to be registered.

-----------------------------------------------------------------------------*/

module mkFindFIFOBypassM (FindFIFOM#(t1,t2)) provisos (Bits#(t1,szt1));

   Reg#(Maybe#(t1)) data();
   mkReg#(Invalid) data_r(data);

   RWire#(void) deq_probe();
   mkRWire deq_probe_r(deq_probe);

   RWire#(t1) enq_probe();
   mkRWire enq_probe_r(enq_probe);

   RWire#(void) clr_probe();
   mkRWire clr_probe_r(clr_probe);

   Bool is_deq = isValid(deq_probe.wget);
   Bool is_enq = isValid(enq_probe.wget);
   Bool is_clr = isValid(clr_probe.wget);
   
   Bool has_data = isValid(data);
   Bool can_enq = is_deq || !has_data;
   Bool can_deq = has_data;

   (* fire_when_enabled, no_implicit_conditions *)
   rule handle_inputs;
      if (is_clr)
	 data <= Invalid;
      else
	 if (is_enq)
	    data <= enq_probe.wget;
	 else
	    if (is_deq)
	       data <= Invalid;
	    else
	       data <= data;
   endrule
   
   method enq(x) if (can_enq) = enq_probe.wset(x);
   method deq() if (can_deq) = deq_probe.wset(?);
   method clear() = clr_probe.wset(?);
   
   method first() if (has_data) = validValue(data);

   method find(f);
      let mx = enq_probe.wget;  // this is maybe x, depending on enq
      let fx = f(validValue(mx)); // if enq, this is f(x)
      
      if (is_enq && isValid(fx))
	 return fx;
      else
      if (has_data)
	 return f(validValue(data));
      else
	 return Invalid;
   endmethod

   method notEmpty() = has_data;

endmodule

