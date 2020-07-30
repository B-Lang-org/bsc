package PriQ;

// NOTE that in the following discussion we shall use the following
// conventions:
// 1.  The head of the queue (the next to be dequeued) is at the right-hand
// end, and has the lowest index (0).
// 2.  A higher priority is indicated by the priority value being higher.
// Entries with higher priority come out earlier.

import RevertingVirtualReg::*;

import QType::*;

// The type of "moves".  The deriving clause tells the compiler to use the
// obvious definitions of equality of moves and their representation in bits.

typedef enum {LEFT, SAME, RIGHT, REPLACE} Move // LEFT means "receives from
           deriving (Eq, Bits);                // left" etc.


// This is the main module definition.  The parameter pipelining is a flag to
// tell whether we wish the implementation to be pipelined, n is the depth of
// the queue to be made, and qe is the type of the elements.  The provisos
// ensure (1) that values of this type can be represented as bits (so that
// they can be stored in registers); (2) that they can be ordered (so that we
// can use the <, >, etc. operators on them).

module mkSizedPriQ#(Bool pipelining, Integer n)(Q#(qe))
   provisos (Bits#(qe,sqe), Ord#(qe));

   // Note: a "tagged union" value of type "Maybe#(a)" is either "Invalid", or
   // "Valid(x)", where x is a value of type a.

   // We declare an array of registers to hold the queue.  They contain
   // Invalid if they are empty, and Valid(v) if they contain the value v.
   Reg#(Maybe#(qe)) queue[n];
   for (Integer i = 0; i<n; i=i+1)
      queue[i] <- mkReg(tagged Invalid); // the registers are all
       		 	                 // empty to start with.

   // A register that tracks whether the saved state is the current state of
   // the queue.
   // Note: we know that this register will always hold the value True at the
   // end of each clock-cycle; that is, the value actually stored in the
   // hardware will never change, so real storage is unnecessary.
   // mkRevertingVirtualReg is intended to exploit this situation.
   Reg#(Bool) queueValid <- mkRevertingVirtualReg(True);

   // Next we declare the interfaces of the pipeline registers, in case we
   // need them: they consist of an array of registers storing moves, and one
   // possibly to store a value to be inserted into the queue.  (The "?" is to
   // prevent irritating warnings from the tool, which otherwise notices that
   // lastV is not initialized when pipelining is False; initializing it here,
   // even to the undetermined value "?", keeps the tool quiet.)
   Reg#(Move) mrs[n];
   Reg#(Maybe#(qe)) lastV = ?;

   // If we are pipelining we instantiate all these registers; if we are not,
   // we shall not use them and we needn't bother.
   if (pipelining)
      begin
	 for (Integer i = 0; i<n; i=i+1)
            mrs[i] <- mkReg(SAME);
	 lastV <- mkRegU;
      end

   // This defines the action which moves elements around in the queue.  Its
   // arguments are the list of moves required, and maybe a value to be
   // enqueued.
   function Action do_moves(Move ms[], Maybe#(qe) v);
      action
	 for (Integer i = 0; i<n; i = i+1)
	    begin
	       // The "asIfc" in the following ensures that the new variables
	       // denote the actual register interface (that is, the normal
	       // register-reading shorthand is inhibited):
	       let self  = asIfc(queue[i]);
	       let left  = asIfc(queue[i+1]);
	       let right = asIfc(queue[i-1]);
	       case (ms[i])
		  LEFT:    self <= (i==n-1 ? Invalid : left);
		  RIGHT:   self <= (i==0 ? (?) : right);
		  REPLACE: self <= v;
		  SAME:    noAction;
	       endcase
	    end
      endaction
   endfunction

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

   // This finds the current entry for a particular index.  If we are
   // pipelining, the definition takes account of the stored moves, reading
   // the appropriate slot; if not, the definition is of course trivial.
   function Maybe#(qe) current_entry(Integer i);
      // Note that unlike the similar code above, we do not use "asIfc" here;
      // so the new variables denote the register contents rather than the
      // interface:
      let self  = queue[i];
      let left  = queue[i+1];
      let right = queue[i-1];
      if (pipelining)
	 begin
	    let m = mrs[i];
	    case (m)
	       LEFT:    return (i==n-1 ? Invalid : left);
	       SAME:    return self;
	       RIGHT:   return (i==0 ? (?) : right);
	       REPLACE: return lastV;
	    endcase
	 end
      else return self;
   endfunction

   // These next definitions refer to the first and last "real" elements of
   // the queue, and use them to test for emptiness and fulness of the entire
   // queue.
   let firstElement = current_entry(0);
   let lastElement  = current_entry(n-1);
   let notEmpty = (isValid(firstElement));
   let notFull  = (!isValid(lastElement)) || isValid(rw_deq.wget);

   // This next group of four functions computes the move required to deal
   // with the various combinations of enqueue and dequeue requests.  Their
   // arguments are the value to be enqueued (if there is one), and the index
   // of the queue slot concerned.  The queue is sorted in descending order of
   // priority (right to left), using the >= ordering.

   // If neither an enqueue nor a dequeue request has been received, all the
   // elements stay the same.
   function Move neither(Integer i) = SAME;

   // If only a dequeue is to happen, each element is replaced by the one to
   // its left.
   function Move deq_only(Integer i) = LEFT;

   // If only an enqueue is to happen, the new element must be slotted in at
   // the appropriate place; all to the left of it are replaced by the one to
   // their right, while all to the right of it stay the same.
   function Move enq_only(qe v, Integer i);
      let self = current_entry(i);
      let right =current_entry(i-1);
      if (i==0)
	 return (case (self) matches
		    tagged Invalid:  return REPLACE;
		    tagged Valid .s: return (s>=v) ? SAME : REPLACE;
		 endcase);
      else
	 return (case (tuple2(self,right)) matches
		    {.*, tagged Invalid}:
                            return SAME;
		    {tagged Invalid, tagged Valid .p}:
					return ((p>=v) ? REPLACE : RIGHT );
		    {tagged Valid .s, tagged Valid .p}:
					 return ((s>=v) ? SAME :
				       		 (p>=v) ? REPLACE : RIGHT );
		 endcase);
   endfunction

   // Finally comes the function to handle simultaneous enqueue and dequeue.
   function Move both(qe v, Integer i);
      let self = current_entry(i);
      let left  = (i==n-1 ? Invalid : current_entry(i+1));
      return (case (tuple2(left,self)) matches
		 {.*, tagged Invalid}:
                         return SAME;
		 {tagged Valid .l, tagged Valid .s}:
				     return ((l>=v) ? LEFT :
					     (s>=v || i==1) ? REPLACE : SAME );
		 {tagged Invalid, tagged Valid .s}:
				     return ((s>=v || i==1) ? REPLACE : SAME );
	      endcase);
   endfunction

   // This is the rule which does all the work.  It is essential that it fires
   // on every clock, so we specify attributes which the tool will check (and
   // give an error report if they are not satisfied).

   (* no_implicit_conditions, fire_when_enabled *)
   rule process_requests;
      // We define two arrays of moves: the first will be initialised with the
      // moves required by the incoming commands, while the second will be
      // used to control the queue elements.
      Move stage1_moves[n];
      Move stage2_moves[n];

      // These next two variable hold incoming queue entries: the first is
      // initialised from the enq method; the second will be stored in the
      // appropriate queue element.
      Maybe#(qe) stage1_v = rw_enq.wget;
      Maybe#(qe) stage2_v;

      // We now choose the appropriate function from the group defined above,
      // by testing the values on the RWires.  NOTE that in BSV arguments can
      // be supplied to functions in stages.  Here "enq_only" and "both" need
      // two arguments; we give them one here, and then they require just one
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
      for (Integer i = 0; i<n; i=i+1)
	 action
	    stage1_moves[i] = the_fun(i);
	 endaction

      // If we are pipelining, we read the stage_2 values from their registers,
      // and store the stage_1 values in their place.  If not pipelining, we
      // copy the stage_1 values to their stage_2 counterparts.
      if (pipelining)
	 action
	    for (Integer i = 0; i<n; i=i+1)
	       action
		  (mrs[i]) <= stage1_moves[i];

		  let m2 = mrs[i];
		  stage2_moves[i] = m2;
	       endaction

	    lastV <= stage1_v;
	    stage2_v = lastV;
	 endaction
      else
	 begin
	    for (Integer i = 0; i<n; i=i+1)
	       stage2_moves[i] = stage1_moves[i];
	    stage2_v = stage1_v;
	 end

      // Now that all the stage_2 values are set, we apply them to the queue.
      do_moves(stage2_moves, stage2_v);

      // This next assignment is taken care of by mkRevertingVirtualReg:
      //       queueValid <= True;
   endrule

   // Finally come the methods.

   // The enq method merely sets the relevant rwire (assuming that it will be
   // processed "later" in the cycle, by the rule defined above).
   method enq(x) if (notFull);
      action
         queueValid <= False;
	 rw_enq.wset(x);
      endaction
   endmethod

   // The "deq" method sets the relevant rwire; the value set is irrelevant.
   method deq() if (notEmpty);
      action
         queueValid <= False;
	 rw_deq.wset(?);
      endaction
   endmethod

   // The first value is in the first queue element, if it's not empty:
   method first() if (firstElement matches tagged Valid .v &&& queueValid);
      return (v);
   endmethod

   // The clear method empties each element, either immediately or (if
   // pipelining) by setting the pipeline registers appropriately.
   method Action clear();
      if (pipelining)
	 action
	    for (Integer i = 0; i<n; i=i+1)
	       (mrs[i]) <= REPLACE;
	    lastV <= tagged Invalid;
	 endaction
      else
	 action
	    Move ms[n];
 	    for (Integer i = 0; i<n; i=i+1)
	       ms[i] = REPLACE;
	    do_moves(ms, tagged Invalid);
	 endaction
   endmethod

endmodule

endpackage
