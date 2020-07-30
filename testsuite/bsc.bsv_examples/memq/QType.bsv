package QType;

// The following is the queue interface, with our usual four methods. "a" is
// the type of the queue entries.

// NOTE: Though this assumption is not embodied in this definition, we shall
// be assuming in the implementation that these methods provide at all times a
// coherent snapshot of the queue.  That is, for example, the "first" method
// shows a different top entry immediately after a cycle in which the
// "dequeue" method is enabled.  The actual requirements might eventually be
// different from this.

interface Q #(type a);
   method Action enq(a x1);
   method Action deq();
   method a first();
   method Action clear();
endinterface: Q

endpackage
