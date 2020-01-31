package CompletionBuffer;

export CompletionBuffer(..);
export CBToken;
export mkCompletionBuffer;

import RegFile :: *;
import GetPut  :: *;
import Counter :: *;

// CompletionBuffer
//
// A CompletionBuffer is like a FIFO except that entering elements
// can be done out-of-order.
// To enter something into the completion buffer a token is necessary.
// A token can be obtained with the "reserve" method.  This token
// is then used in the "complete" method to enter the actual item.
// Finally, the "drain" method takes items out of the buffer; the items
// are delivered in the order of the tokens that were checked out.
//
// The "n" represents the size of the completion buffer, and "a" is the
// item type.
//
interface CompletionBuffer #(type n, type a);
    interface Get#(CBToken#(n)) reserve;
    interface Put#(Tuple2#(CBToken#(n), a)) complete;
    interface Get#(a) drain;
endinterface: CompletionBuffer

// CBToken
//
// The CBToken type is just an alias.
//
typedef Bit#(TLog#(n)) CBToken#(type n);

// utility function
function Bool isPowerOf2(Integer n);
   return (n == (2 ** (log2(n))));
endfunction

// mkCompletionBuffer
//
module mkCompletionBuffer (CompletionBuffer#(n, a))
  provisos (Bits#(a, sa), Log#(n, ln), Add#(1, ln, ln1));

    let hi = fromInteger(valueOf(n) - 1);

    function Action incr(Reg#(Bit#(ln)) r);
     action
       if (isPowerOf2(valueOf(n)))
           r <= r + 1;  // counter wraps automagically
       else
           r <= ((r == hi) ? 0 : r + 1);
     endaction
    endfunction

    RegFile#(Bit#(ln), Maybe#(a)) buff <- mkRegFileWCF(0, hi);
    Reg#(Bit#(ln)) i <- mkReg(0);       // input index
    Reg#(Bit#(ln)) o <- mkReg(0);       // output index
    Counter#(ln1) n <- mkCounter(0);    // number of filled slots

    interface Get reserve;
        method ActionValue#(CBToken#(n)) get()
          if (n.value() <= hi);
            incr(i);
            n.up();
            buff.upd(i, tagged Invalid);
            return i;
        endmethod
    endinterface

    interface Put complete;
        method Action put(Tuple2#(CBToken#(n), a) p);
           match { .t, .a } = p;
           buff.upd(t, tagged Valid a);
        endmethod
    endinterface

    interface Get drain;
        method ActionValue#(a) get()
          if (n.value() > 0 &&& buff.sub(o) matches tagged Valid .x);
            incr(o);
            n.down();
            return x;
        endmethod
    endinterface

endmodule: mkCompletionBuffer

endpackage: CompletionBuffer
