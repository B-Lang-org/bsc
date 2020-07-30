package PriQ1;

// NOTE that in the following discussion we shall use the following
// conventions:
// 1.  The head of the queue (the next to be dequeued) is at the right-hand
// end, and has the lowest index (1).
// 2.  A higher priority is indicated by the priority value being higher.
// Entries with higher priority come out earlier.

import QType::*;

// The type of "moves".  The deriving clause tells the compiler to use the
// obvious definition of equality of moves.

typedef enum {LEFT, SAME, RIGHT, REPLACE} Move // LEFT means "receives from
           deriving (Eq);                      // left" etc.


// We shall need a couple of "constant" registers, which always return their
// initial contents, and ignore any attempt to overwrite them.  This is the
// module that constructs them; note that they involve no state, only wires.

module mkConstReg#(a x)(Reg#(a));
   method a _read();
      return x;
   endmethod
   method Action _write(a y) = noAction;
endmodule

// This is the main module definition.  The parameter n is the depth of the
// queue to be made, and qe is the type of the elements.  The provisos ensure
// (1) that values of this type can be represented as bits (so that they can
// be stored in registers); (2) that they can be ordered (so that we can use
// the <, >, etc. operators on them); (3) that they have "max" and "min values
// (because we shall want to use one of these in one of the end sentinel
// constant-registers).

module mkSizedPriQ#(Integer n)(Q#(qe))
   provisos (Bits#(qe,sqe), Ord#(qe), Bounded#(qe));

   // Note: a value of type "Maybe#(a)" is either "Invalid", or "Valid(x)",
   // where x is a value of type a.

   // We declare an array of registers to hold the queue, with an extra
   // constant sentinel register at each end.  The ordinary registers contain
   // Invalid if they are empty, and Valid(v) if they contain the value v.  The 
   // constant register at the low end is always non-empty (and its contents
   // will be at least >= than anything it is compared with); the one at the
   // high end is always empty.
   Reg#(Maybe#(qe)) queue[n+2];
   for (Integer i = 0; i<n+2; i=i+1)
      begin
	 let m = (i==0 ? mkConstReg(tagged Valid maxBound) :
		  i>n  ? mkConstReg(tagged Invalid) :
		  mkReg(tagged Invalid)); // the actual registers are all
				          // empty to start with.
	 let entry <- m;   //instantiate an appropriate register, and
	 queue[i] = entry; //initialise the array entry with it.
      end


   // This defines the action which moves elements around in the queue.  Its
   // arguments are the list of moves required, and maybe a value to be
   // enqueued. 
   function Action do_moves(List#(Move) ms, Maybe#(qe) v);
      action
	 for (Integer i = 1; i <= n; i = i+1)
	    begin
	       let self  = queue[i];
	       let left  = queue[i+1];
	       let right = queue[i-1];
	       case (ms[i])
		  LEFT:    self <= left;
		  RIGHT:   self <= right;
		  REPLACE: self <= v;
		  SAME:    noAction;
	       endcase
	    end
      endaction
   endfunction

   // This finds the current entry for a particular index.  Its definition is
   // trivial now, but will become more interesting when we pipeline.

   function Maybe#(qe) current_entry(Integer i);
      let e = queue[i];
      return e;
   endfunction
   
   // These next definitions refer to the first and last "real" elements of
   // the queue, and use them to test for emptiness and fulness of the entire
   // queue.
   let firstElement = current_entry(1);
   let lastElement  = current_entry(n);
   let notEmpty = (isValid(firstElement));
   let notFull  = (!isValid(lastElement));

   // NOTE: the BSV tool schedules many rules and methods in each clock cycle,
   // but the overall effect is always as if they happened strictly
   // sequentially within the cycle.  (This makes it much easier to recognise
   // resource conflicts, rather than debugging a race condition.)  An RWire
   // is implemented purely with wires, but looks rather like a register,
   // except that its contents always revert to "Invalid" at the end of each
   // clock cycle.  Here we use them for communication between the interface
   // methods and the processing rule (which will be executed "later" in the
   // cycle). 

   // If the value in this RWire is not Invalid, it indicates that we have
   // accepted an "enq" call a little earlier in the cycle, in which case it
   // holds Valid(the value enqueued): 
   RWire#(qe) rw_enq();
   mkRWire the_rw_enq(rw_enq);

   // If the value in this RWire is not Invalid, it indicates that we have
   // accepted an "deq" call a little earlier; the actual Valid value is
   // irrelevant, so no bits are reserved for it:
   RWire#(Bit#(0)) rw_deq();
   mkRWire the_rw_deq(rw_deq);

   // This next group of four functions computes the move required to deal
   // with the various combinations of enqueue and dequeue requests.  Their
   // arguments are the value to be enqueued (if there is one), and the index
   // of the queue slot concerned.

   function Move enq_only(qe v, Integer i);
      let self = current_entry(i);
      let right =current_entry(i-1);
      return (case (tuple2(self,right)) matches
		 {.*, tagged Invalid}: 
                         return SAME;
		 {tagged Invalid, tagged Valid .p}:
				     return   ((p>=v) ? REPLACE : RIGHT );
		 {tagged Valid .s, tagged Valid .p}:
				      return   ((s>=v) ? SAME :
						(p>=v) ? REPLACE : RIGHT );
	      endcase);
   endfunction

   function Move deq_only(Integer i) = LEFT;

   function Move both(qe v, Integer i);
      let self = current_entry(i);
      let left  = current_entry(i+1);
      return (case (tuple2(left,self)) matches
		 {.*, tagged Invalid}: 
                         return SAME;
		 {tagged Valid .l, tagged Valid .s}:
				      return   ((l>=v) ? LEFT :
						(s>=v) ? REPLACE : SAME );
		 {tagged Invalid, tagged Valid .s}:
				     return   ((s>=v) ? REPLACE : SAME );
	      endcase);
   endfunction

   function Move neither(Integer i) = SAME;

   // This is the rule which does all the work.  It is essential that it fires
   // on every clock, so we specify attributes which the tool will check (and
   // give an error report if they are not satisfied).
      
   (* no_implicit_conditions, fire_when_enabled *)
   rule process_requests;
      // Define an array of moves.
      Move ms[n+1];
      // Choose the appropriate function from the group defined above, by
      // testing the values on the RWires.  NOTE that in BSV arguments can be
      // supplied to functions in stages.  Here enq_only and both needed two
      // arguments; we give them one here, and then they require just one
      // more, exactly like the other two functions.
      let the_fun =
          (case (tuple2(rw_enq.wget, rw_deq.wget)) matches
	      {tagged Valid .v, tagged Invalid}:  return enq_only(v);
	      {tagged Invalid,  tagged Valid .*}: return deq_only;
	      {tagged Valid .v, tagged Valid .*}: return both(v);
	      {tagged Invalid,  tagged Invalid}:  return neither;
	   endcase);

      // This loop applies the chosen function (in parallel) to all the
      // slots, initializing the array of moves
      for (Integer i = 1; i<=n; i=i+1)
	 action
	    ms[i] = the_fun(i);
	 endaction
      
      // Now that all the moves are known, we do them.
      do_moves(ms, rw_enq.wget);
   endrule

   // Finally come the methods.
   
   // The enq method merely sets the relevant rwire (assuming that it will be
   // processed "later" in the cycle, by the rule defined above).
   method enq(x) if (notFull);
      action
	 rw_enq.wset(x);
      endaction
   endmethod

   // The "deq" method sets the relevant rwire; the value set is irrelevant.
   method deq() if (notEmpty);
      action
	 rw_deq.wset(?);
      endaction
   endmethod

   // The first value is in the first queue element, if it's not empty:
   method first() if (firstElement matches tagged Valid .v);
      return (v);
   endmethod

   // The clear method empties each element.
   method Action clear();
      action
	 Move ms[n+1];
 	 for (Integer i = 1; i<=n; i=i+1)
	    ms[i] = REPLACE;
	 do_moves(ms, tagged Invalid);
      endaction
   endmethod

endmodule

endpackage
