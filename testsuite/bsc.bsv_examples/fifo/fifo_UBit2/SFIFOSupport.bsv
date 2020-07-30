import List::*;  // List::select;
import UBit::*;

interface SFIFO #(type t);
    method Action enq(t val);
    method t first();
    method Action deq();
    method Action clear();
    method Bool isFull();
    method Bool isEmpty();
endinterface

// Max size of the 
module mkSFIFO #(Integer size) (SFIFO#(t)) provisos (Bits#(t, ts));
  List#(Reg#(t)) rs = replicate(size, ?);
  Integer i;
  for (i=0; i<size; i=i+1)
    begin
      Reg#(t) r();
      mkRegU the_r(r);
      rs[i] = asReg(r);
    end

  Reg#(UBit) head();
  mkUBitReg#(log2(size), 0) the_head(head);

  Reg#(UBit) tail();
  mkUBitReg#(log2(size), 0) the_tail(tail);

  UBit maxptr = fromInteger(size - 1);
  UBit minptr = 0;

  function UBit incr(UBit ptr);
      incr = (ptr == maxptr ? minptr : ptr + 1);
  endfunction
  function UBit decr(UBit ptr);
      decr = (ptr == minptr ? maxptr : ptr - 1);
  endfunction

  Bool notEmpty = head != tail;
  Bool notFull  = incr(tail) != head;

  function t get(UBit ptr);
      get = (uBitSelect(rs, ptr))._read;
  endfunction

  function Action put(UBit ptr, t v);
    action
      (uBitSelect(rs, ptr)) <= v;
    endaction
  endfunction
  
  method enq(x) if (notFull) ;
    action
      put(tail, x);
      tail <= incr(tail);
    endaction
  endmethod: enq

  method first() if (notEmpty) ;
      return (get(head));
  endmethod: first

  method deq() if (notEmpty) ;
    action
      head <= incr(head);
    endaction
  endmethod: deq

  method clear() ;
    action
      head <= minptr;
      tail <= minptr;
    endaction
  endmethod: clear

  method isFull();
      return (!notFull);
  endmethod

  method isEmpty();
      return (!notEmpty);
  endmethod

endmodule

