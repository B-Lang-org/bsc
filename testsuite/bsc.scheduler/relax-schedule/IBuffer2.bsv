import Interfaces::*;
import BaseTypes::*;

import FIFO::*;
import Vector::*;
import List::*;
import BypassFIFO::*;

// XXX345 the synthesize below removes urgency cycle:
// (* synthesize *)
module mkCacheAddrQueue(FIFO#(IAddress));
  FIFO#(IAddress) caq <- mkBypassFIFO;
  return caq;
endmodule

// XXX345 the synthesize below removes urgency cycle:
// (* synthesize *)
module mkResponseQueue(FIFO#(IBus#(Tuple2#(PackedInstruction, IAddress), 1)));
  FIFO#(IBus#(Tuple2#(PackedInstruction, IAddress), 1)) rq <- mkBypassFIFO;
  return rq;
endmodule

(* synthesize *)
module mkIBuffer(IBuffer#(IAddress, PackedInstruction, 1, 1));
  
// don't use bypassFIFO to avoid race condition
  FIFO#(IAddress) cacheAddrQueue <- mkCacheAddrQueue;
  FIFO#(IBus#(Tuple2#(PackedInstruction, IAddress), 1)) responseQueue <- mkResponseQueue;
//  FIFO#(IAddress) cacheAddrQueue <- mkFIFO;
//  FIFO#(IBus#(Tuple2#(PackedInstruction, IAddress), n)) responseQueue <- mkFIFO;

  function a fst(Tuple2#(a,b) x);
    match{.a1,.b1} = x;
    return(a1);
  endfunction: fst

  function (List#(Predicated#((Tuple2#(PackedInstruction, IAddress)))))
      subTrans(IAddress ia, List#(Predicated#(PackedInstruction)) li);
      let next_ia = ia + 4;
      case (decodeList(li)) matches
           tagged Invalid : return Nil;
           tagged Valid {.hd, .tl} : begin
                             return (List::cons(
                                       (isJust(hd))?Just(tuple2(unJust(hd),ia)): Nothing,
                                      subTrans(next_ia, tl)));                            
                           end


      endcase
  endfunction: subTrans


  function Vector#(1,Predicated#(Tuple2#(PackedInstruction, IAddress)))
       doTrans (Tuple2#(IAddress, Vector#(1,Predicated#(PackedInstruction))) x);
     match{.ia, .ln} = x;
     let fli = subTrans (ia, toList(ln));
     return (toVector(fli));
  endfunction: doTrans

  method Action handleCacheResponse(Tuple2#(IAddress, Vector#(1, Predicated#(PackedInstruction))) x);
     responseQueue.enq(doTrans(x));
  endmethod: handleCacheResponse

  method ActionValue#(IBus#(Tuple2#(PackedInstruction, IAddress), 1)) iBufferResponse();
    responseQueue.deq();
    return (responseQueue.first);   
  endmethod: iBufferResponse

  method Action handleIBufferRequest(IAddress x);
    IAddress new_x = fst (split(x));
    cacheAddrQueue.enq(new_x);
  endmethod: handleIBufferRequest

  method ActionValue#(IAddress) cacheRequest();
    cacheAddrQueue.deq();
    return (cacheAddrQueue.first);   
  endmethod: cacheRequest

  method Action flush();
    cacheAddrQueue.clear();
    responseQueue.clear();
  endmethod: flush

  method Action flushAddress(IAddress x);
    //XXX This does the wrong thing
    cacheAddrQueue.clear();
    responseQueue.clear();
  endmethod: flushAddress

endmodule: mkIBuffer
