package IBus;

import Interfaces::*;
import Vector::*;

import FIFOF::*;

function Tuple2#(Maybe#(a), Maybe#(b)) maybeUnzip(Maybe#(Tuple2#(a, b)) data);

  return case (data) matches
    tagged Nothing:
      return tuple2(Nothing, Nothing);
    tagged Just .t:
      return tuple2(Just(t.fst), Just(t.snd));
    endcase;
endfunction


typedef IBus#(Either#(a,b), n) EBus#(type a, type b, type n);

function Tuple2#(IBus#(a, m), IBus#(b, m)) 
            threadEBus (EBus#(a, b, n) in1, EBus#(a, b, n) in2)
    provisos (Add#(n, n, m));

  IBus#(a, m) r1 = replicate(?);
  IBus#(b, m) r2 = replicate(?);
  
  for (Integer k = 0; k < valueof(n); k = k + 1)
  begin
    r1[k] = case (in1[k]) matches
      tagged Nothing:
        return Nothing;
      tagged Just .e:
        return case (e) matches
	  tagged Left .x:
	    return Just(x);
	  tagged Right .y:
	    return Nothing;
	endcase;
     endcase;
     r2[k] = case (in2[k]) matches
       tagged Nothing:
         return Nothing;
       tagged Just .e:
         return case (e) matches
	   tagged Left .x:
	     return Nothing;
	   tagged Right .y:
	     return Just(y);
	  endcase;
     endcase;
  end

  return tuple2(r1, r2);

endfunction

function Tuple2#(IBus#(a, n), IBus#(b, n)) 
           splitEBus(EBus#(a, b, n) inbus);
	   
  IBus#(a, n) r1 = replicate(?);
  IBus#(b, n) r2 = replicate(?);
  
  for (Integer k = 0; k < valueof(n); k = k + 1)
  begin
    case (inbus[k]) matches
      tagged Nothing:
      begin
        r1[k] = Nothing;
	r2[k] = Nothing;
      end
      tagged Just .e:
	case (e) matches
	  tagged Left .x:
	  begin
            r1[k] = Just(x);
	    r2[k] = Nothing;
	  end
	  tagged Right .y:
	  begin
            r1[k] = Nothing;
	    r2[k] = Just(y);
	  end
        endcase
    endcase
  end
  
  return tuple2(r1, r2);
endfunction

//This biases to Left in the case of a collision. 
//IE the Right value will be discarded if Left is present.

function EBus#(a, b, n) 
      	    joinEBus_exclusive(IBus#(a, n) inl, IBus#(b, n) inr);

  EBus#(a, b, n) res = replicate(?);
  
  for (Integer k = 0; k < valueof(n); k = k + 1)
  begin
    res[k] = case (inl[k]) matches
      tagged Nothing:
        return case (inr[k]) matches
	  tagged Nothing:
	    return Nothing;
	  tagged Just .y:
	    return Just(Right(y));
	endcase;
      tagged Just .x:
        return Just(Left(x));
    endcase;
  end
  
  return res;

endfunction

//This scheme guarantees no lost data, but thus doubles the size of the joined bus.

function EBus#(a, b, m) 
      	    joinEBus_double(IBus#(a, n) inl, IBus#(b, n) inr)
  provisos (Add#(n, n, m));

  EBus#(a, b, m) res = replicate(?);
  
  for (Integer k = 0; k < (valueof(m) - 1); k = k + 2) //Note: Stepping by 2
  begin
    case (inl[k]) matches
      tagged Nothing:
        case (inr[k]) matches
	  tagged Nothing:
	  begin
	    res[k] = Nothing;
	    res[k + 1] = Nothing;
	  end
	  tagged Just .y:
	  begin
	    res[k] = Nothing;
	    res[k + 1] = Just(Right(y));
	  end
	endcase
      tagged Just .x:
        case (inr[k]) matches
	  tagged Nothing:
	  begin
	    res[k] = Just(Left(x));
	    res[k + 1] = Nothing;
	  end
	  tagged Just .y:
	  begin
	    res[k] = Just(Left(x));
	    res[k + 1] = Just(Right(y));
	  end
	endcase
    endcase
  end
  
  return res;

endfunction

interface Queue#(parameter type a);
  method ActionValue#(Maybe#(a)) dequeue();
  method Action enqueue(a data);
  method Action clear();
endinterface


module mkIQueue (Queue#(a)) provisos (Bits#(a, s));

  FIFOF#(a) f <- mkUGFIFOF;

  method ActionValue#(Maybe#(a)) dequeue();
    if (f.notEmpty)
       f.deq();
    return (f.notEmpty)?Just(f.first):Nothing;
  endmethod

  method Action enqueue(a data);
    f.enq(data);
  endmethod

  method Action clear();
    f.clear();
  endmethod

endmodule


endpackage
