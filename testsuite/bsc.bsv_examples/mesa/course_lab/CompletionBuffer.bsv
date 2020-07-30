package CompletionBuffer;

import RegFile::*;
import GetPut::*;
import Counter::*;
import List::*;

// The CompletionBuffer interface:
interface CompletionBuffer #(type n, type a);
   method Get#(CBToken#(n)) reserve();
   method Put#(Tuple2#(CBToken#(n), a)) complete();
   method Get#(a) drain();
endinterface: CompletionBuffer

typedef Bit#(TLog#(n)) CBToken #(type n);

function Bool isPowerOf2(Integer n);
   return (n == exp(2, log2(n)));
endfunction: isPowerOf2

module mkCompletionBuffer(CompletionBuffer#(n, a))
   provisos (Bits#(a, sa), Log#(n, ln), Log#(n, TLog#(n)), Add#(1, ln, ln1));
   let hi =  fromInteger(valueOf(n));
   // A function to increment the pointer, with wraparound:
   function Action incr(Reg#(Bit#(ln)) r);
      return
      (isPowerOf2(valueOf(n)) ?
       action r <= r + 1; endaction
       : action r <= (r == hi-1 ? 0 : r + 1); endaction);
   endfunction: incr

   // The data vector:
   RegFile#(Bit#(ln), a) buff();
   mkRegFileWCF#(0, hi-1) the_buff(buff);

   // The flags vector:
   // The RWires for both its set operations:
   List#(RWire#(void)) sets = replicate(hi, ?);
   List#(RWire#(void)) clears = replicate(hi, ?);
   // the vector itself:
   List#(Reg#(Bool)) flags = replicate(hi, ?);
   // Instantiate it all:
   for (Integer j = 0; j<hi; j=j+1)
      begin
         RWire#(void) s();
         mkRWire the_s(s);
         sets[j] = s;

         RWire#(void) c();
         mkRWire the_c(c);
         clears[j] = c;

         Reg#(Bool) f();
         mkReg#(False) the_f(f);
         flags[j] = asReg(f);

         (* no_implicit_conditions, fire_when_enabled *)
         rule update_flag;
            let s = (sets[j]).wget;
            let c = (clears[j]).wget;

            if (isValid(s)) f <= True;
            else if (isValid(c)) f <= False;
            else noAction;
         endrule
      end

   // The input pointer:
   Reg#(Bit#(ln)) i();
   mkReg#(0) the_i(i);

   // The output pointer:
   Reg#(Bit#(ln)) o();
   mkReg#(0) the_o(o);

   // The counter of how many slots are used:
   Counter#(ln1) n();
   mkCounter#(0) the_n(n);

   // Reserve a slot; returns the tag:
   interface Get reserve;
      method get() if (n.value < hi) ;
         actionvalue
            incr(i);
            n.up;
            (select(clears,i)).wset(?);
            return(i);
         endactionvalue
      endmethod: get
   endinterface: reserve

   // Place data in slot:
   interface Put complete;
      method put(x);
         action
            match {.t,.a} = x;
            (buff.upd)(t, a);
            (select(sets,t)).wset(?);
         endaction
      endmethod: put
   endinterface: complete

   // Retrieve data from slot if present, and deallocate:
   interface Get drain;
      method get() if (select(flags,o) matches .b &&& b && n.value > 0);
         actionvalue
            incr(o);
            n.down;
            return((buff.sub)(o));
         endactionvalue
      endmethod: get
   endinterface: drain
endmodule: mkCompletionBuffer

endpackage: CompletionBuffer
