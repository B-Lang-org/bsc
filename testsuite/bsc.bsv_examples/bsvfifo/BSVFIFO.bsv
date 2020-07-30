package BSVFIFO;

import FIFO::*;

// This example implements a FIFO in BSV (instead of as a primitive element)

// The following is the imported FIFO interface, with the usual four methods:
// interface FIFO #(type a);
//   method Action enq(a x1);
//   method Action deq();
//   method a first();
//   method Action clear();
// endinterface: FIFO

// We shall need a couple of "constant" registers, which always return their
// initial contents, and ignore any attempt to overwrite them:
module mkConstReg#(a x)(Reg#(a));
   method a _read();
      return x;
   endmethod
   method Action _write(a y);
      action
      endaction
   endmethod
endmodule

// This is the main definition.  The parameter n is the depth of the queue to
// be made, and a is the type of the elements: the proviso ensures that values
// of this type can be stored in registers.

module mkSizedBSVFIFO#(Integer n)(FIFO#(a))
   provisos (Bits#(a,sa));

   // We declare an array of registers to hold the queue, with an extra
   // constant sentinel register at each end.  The ordinary registers contain
   // Invalid if they are empty, and Valid(v) if they contain the value v.  The 
   // constant register at the low end is always non-empty (though its
   // contents are irrelevant; the one at the high end is always empty.
   Reg#(Maybe#(a)) queue[n+2];
   for (Integer i = 0; i<n+2; i=i+1)
      begin
	 let m = (i==0 ? mkConstReg(Valid(?)) :
		  i>n  ? mkConstReg(Invalid) :
		  mkReg(Invalid));
	 Reg#(Maybe#(a)) r();
	 m the_r(r);
	 queue[i] = asReg(r);
      end
   
   // These next definitions refer to the first and last "real" elements of
   // the queue, and use them to test for emptiness and fulness of the entire
   // queue:
   let firstElement = queue[1];
   let lastElement  = queue[n];
   let notEmpty = (isValid(firstElement));
   let notFull  = (!isValid(lastElement));

   // If the value in this RWire is not Invalid, it indicates that we have
   // accepted an "enq" call a little earlier (in the TRS sense), in which
   // case it holds Valid(the value enqueued):
   RWire#(a) rw_enq();
   mkRWire the_rw_enq(rw_enq);

   // If the value in this RWire is not Invalid, it indicates that we have
   // accepted an "deq" call a little earlier; the actual Valid value is
   // irrelevant, so no bits are reserved for it:
   RWire#(Bit#(0)) rw_deq();
   mkRWire the_rw_deq(rw_deq);


   // The (* fire_when_enabled *) attributes on the internal rules
   // instruct the compiler to check that nothing (i.e. a conflict) 
   // blocks the annotated rules from firing when their predicate is satisfied


   // This rule deals with the situation when an "enq" has been accepted but
   // not a "deq".  Each queue element is considered (in parallel); the one
   // which is empty, but whose predecessor is full, stores the new value.
   // Note that there must be such an element, or the "enq" would not have
   // been accepted in the first place.
   (* fire_when_enabled *)
   rule enq_rule (rw_enq.wget matches tagged Valid .v &&& rw_deq.wget matches tagged Invalid);
      for (Integer i = 1; i<=n; i=i+1)
	 action
	    let self = asReg(queue[i]);
	    let previous =asReg(queue[i-1]);
	    if (isValid(previous) && !isValid(self))
	       self <= Valid(v);
	 endaction
   endrule

   // This rule covers the case of a "deq" but no "enq".  Each element takes
   // the value previously held by the next one.
   (* fire_when_enabled *)
   rule deq_rule (rw_enq.wget matches tagged Invalid &&& rw_deq.wget matches tagged Valid .x);
      for (Integer i = 1; i<=n; i=i+1)
	 action
	    let self = asReg(queue[i]);
	    let next = asReg(queue[i+1]);
	    self <= next;
	 endaction
   endrule

   // This rule deals with an "enq" and a "deq" in the same cycle.  Each
   // element assumes the value of the next one, except for the one which is
   // to store the new value:
   (* fire_when_enabled *)
   rule enqdeq_rule (rw_enq.wget matches tagged Valid .v &&& rw_deq.wget matches tagged Valid .x);
      for (Integer i = 1; i<=n; i=i+1)
	 action
	    let self = asReg(queue[i]);
	    let next = asReg(queue[i+1]);
	    if (isValid(self) && !isValid(next))
	       self <= Valid(v);
	    else
	       self <= next;
	 endaction
   endrule

   // Finally come the methods.
   
   // The enq method merely sets the relevant rwire (assuming that this will
   // cause the appropriate rule to fire, in the same clock cycle (in a later
   // transition, from the TRS point of view):
   method enq(x) if (notFull);
      action
	 rw_enq.wset(x);
      endaction
   endmethod

   // The "deq" method sets the relevant rwire; the value set is irrelevant:
   method deq() if (notEmpty);
      action
	 rw_deq.wset(?);
      endaction
   endmethod

   // The first value is in the first queue element, if it's not empty:
   method first() if (queue[1] matches .r &&& r matches tagged Valid .v);
      return (v);
   endmethod

   // The clear method empties (in parallel) each element:
   method Action clear();
      action
	 for (Integer i = 1; i<=n; i=i+1)
	    (queue[i]) <= Invalid;
      endaction
   endmethod

endmodule

endpackage
