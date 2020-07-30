package PriQ2;

import QType::*;

// This time we shall be storing moves in the pipeline register, so they need
// to be reprentable as bits.  We let the tool choose the obvious
// representation. 
typedef enum {LEFT, SAME, RIGHT, REPLACE} Move
           deriving (Eq, Bits);


module mkConstReg#(a x)(Reg#(a));
   method a _read();
      return x;
   endmethod
   method Action _write(a y) = noAction;
endmodule

module mkSizedPriQ#(Integer n)(Q#(qe))
   provisos (Bits#(qe,sqe), Ord#(qe), Bounded#(qe));

   Reg#(Maybe#(qe)) queue[n+2];
   for (Integer i = 0; i<n+2; i=i+1)
      begin
	 let m = (i==0 ? mkConstReg(tagged Valid maxBound) :
		  i>n  ? mkConstReg(tagged Invalid) :
		  mkReg(tagged Invalid));
	 let entry <- m;
	 queue[i] = entry;
      end

   // Now the moves are to be stored in an array of registers (the pipeline
   // buffer); so declare and instantiate the array.
   Reg#(Move) ms[n+2];
   for (Integer i = 0; i<n+2; i=i+1)
      begin
	 let m = (i==0 ? mkConstReg(SAME) :
		  i>n  ? mkConstReg(SAME) :
		  mkReg(SAME));
	 let move <- m;
         ms[i] = move;
      end

   // The remaining part of the pipeline buffer stores the value to be
   // enqueued, if one has arrived during the previous cycle.
   Reg#(Maybe#(qe)) lastV <- mkRegU;

   function Action do_moves(List#(Reg#(Move)) msr, Maybe#(qe) v);
      action
	 for (Integer i = 1; i <= n; i = i+1)
	    begin
	       let m = msr[i];
	       Reg#(Maybe#(qe)) self  = queue[i];
	       Reg#(Maybe#(qe)) left  = queue[i+1];
	       Reg#(Maybe#(qe)) right = queue[i-1];
	       case (m)
		  LEFT:    self <= left;
		  RIGHT:   self <= right;
		  REPLACE: self <= v;
		  SAME:    noAction;
	       endcase
	    end
      endaction
   endfunction

   // This finds the current entry for a particular index.  Its definition now
   // takes account of the stored moves, reading the appropriate slot.
   function Maybe#(qe) current_entry(Integer i);
      let self  = queue[i];
      let left  = queue[i+1];
      let right = queue[i-1];
      let m = ms[i];
      case (m)
	 LEFT:    return left;
	 SAME:    return self;
	 RIGHT:   return right;
	 REPLACE: return lastV;
      endcase
   endfunction
   
   let firstElement = current_entry(1);
   let lastElement  = current_entry(n);
   let notEmpty = (isValid(firstElement));
   let notFull  = (!isValid(lastElement));

   RWire#(qe) rw_enq();
   mkRWire the_rw_enq(rw_enq);

   RWire#(Bit#(0)) rw_deq();
   mkRWire the_rw_deq(rw_deq);

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

   (* no_implicit_conditions, fire_when_enabled *)
   rule process_requests;
      // We no longer declare the array of moves as a local variable here.
      
      let the_fun =
          (case (tuple2(rw_enq.wget, rw_deq.wget)) matches
	      {tagged Valid .v, tagged Invalid}:  return enq_only(v);
	      {tagged Invalid,  tagged Valid .*}: return deq_only;
	      {tagged Valid .v, tagged Valid .*}: return both(v);
	      {tagged Invalid,  tagged Invalid}:  return neither;
	   endcase);
      
      for (Integer i = 1; i<=n; i=i+1)
	 action
	    // Instead of initialising a local variable, we set the value in
	    // the pipeline buffer.
	    (ms[i]) <= the_fun(i);
	 endaction
      // We store the value to be enqueued.
      lastV <= rw_enq.wget;

      // This call uses the values in the buffers, to revise the queue entries
      // during the next cycle.
      do_moves(ms, lastV);
   endrule

   method enq(x) if (notFull);
      action
	 rw_enq.wset(x);
      endaction
   endmethod

   method deq() if (notEmpty);
      action
	 rw_deq.wset(?);
      endaction
   endmethod

   method first() if (firstElement matches tagged Valid .v);
      return (v);
   endmethod

   // The clear method now sets the pipeline buffers appropriately.
   method Action clear();
      for (Integer i = 1; i<=n; i=i+1)
	 (ms[i]) <= REPLACE;
      lastV <= tagged Invalid;
   endmethod

endmodule

endpackage
