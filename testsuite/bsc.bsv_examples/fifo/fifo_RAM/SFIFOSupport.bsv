import RAM :: *;
import ClientServer :: *;
import GetPut :: *;

interface SFIFO #(type t);
    method Action enq(t val);
    method t first();
    method Action deq();
    method Action clear();
    method Bool isFull();
    method Bool isEmpty();
endinterface

module mkSFIFO #(RAM#(adr,dta) mem, adr minptr, adr maxptr) (SFIFO#(dta))
  provisos(Bits#(dta,dta_sz), Bits#(adr,adr_sz),
	   Literal#(adr), Arith#(adr), Eq#(adr));

  Reg#(adr) head();
  mkReg#(minptr) the_head(head);

  // This is the location of the next data in memory to be copied locally
  Reg#(adr) data_head();
  mkReg#(minptr) the_data_head(data_head);

  Reg#(adr) tail();
  mkReg#(minptr) the_tail(tail);

  // register the data from the fifo, with presence bit
  // Note: This really should be a FIFO as big as the memory latency,
  // for optimal throughput.
  Reg#(Maybe#(dta)) first_elem();
  mkReg#(Invalid) the_first_elem(first_elem);

  function adr incr(adr ptr);
      incr = (ptr == maxptr ? minptr : ptr + 1);
  endfunction
  function adr decr(adr ptr);
      decr = (ptr == minptr ? maxptr : ptr - 1);
  endfunction

  Bool notEmpty = head != tail;
  Bool notFull  = incr(tail) != head;
  Bool notDataEmpty = data_head != tail;

  function Action get(adr i);
    action
      first_elem <= Invalid;  // clear the presence bit
      RAMreq#(adr,dta) req = Read (i);
      mem.request.put(req);
    endaction
  endfunction

  // If we know that there is more data than is stored in our
  // local buffer, then make a request:
  PulseWire claim_mem_pw <- mkPulseWire(); // used to make the enq method
                                           // more urgent than req_dta
  rule req_dta (notDataEmpty && !isValid(first_elem) && !claim_mem_pw);
     get(data_head);
     data_head <= incr(data_head);
  endrule

  (* fire_when_enabled *)
   rule get_dta (True);
      dta res;
      res <- mem.response.get();
      first_elem <= Valid (res);
  endrule

  function Action put(adr i, dta v);
    action
      RAMreq#(adr,dta) req = Write (tuple2(i , v));
      mem.request.put(req);
    endaction
  endfunction

  method enq(x) if (notFull) ;
    action
      put(tail, x);
      tail <= incr(tail);
      claim_mem_pw.send();
    endaction
  endmethod: enq

  method first() if (notEmpty && isValid(first_elem)) ;
      return (validValue(first_elem));
  endmethod: first

  method deq() if (notEmpty) ;
    action
      first_elem <= Invalid;
      head <= incr(head);
    endaction
  endmethod: deq

  method clear() ;
    action
      first_elem <= Invalid;  // clear the presence bit
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
