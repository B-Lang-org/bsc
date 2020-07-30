// This package defines a server replicator -- for simplicity's sake, one
// which always produces three copies (each of which will have higher latency
// than the original).

// Required library packages:
import FIFO::*;
import GetPut::*;
import ClientServer::*;
import Counter::*;

// The counter size ought really to be related (logarithmically) to the
// maximum value of the counter, and thus to the server's latency lat.  But
// for simplicity's sake we give it an ample constant value.
typedef 8 COUNTER_SIZE;
// Two bits are enough to store three tags, one for each copy:
typedef UInt#(2) Tag;

// This module takes one server interface, and provides a tuple of three
// interfaces of the same type.  The lat parameter is the latency of the server.
module mk3Servers#(Integer lat)
   (Server#(a,b) ser, Tuple3#(Server#(a,b), Server#(a,b), Server#(a,b)) provided_i)
   provisos(Bits#(a,sa), Bits#(b,sb));

   // This FIFO stores tags belonging to the requests, while the requests
   // themselves are in flight through the server:
   FIFO#(Tag) tags();
   mkSizedFIFO#(lat) the_tags(tags);

   // This module provides the copy interface numbered i.
   module mkPort#(Tag i)(Server#(a,b));
      // Each port needs a FIFO to store completed results, so that slowness
      // on the part of its client does not block results destined for other
      // servers: 
      FIFO#(b) ofifo();
      mkSizedFIFO#(lat) the_ofifo(ofifo);

      // Similarly, each port counts the number of requests it is processing,
      // to ensure its FIFO can always store all the results if necessary:
      Counter#(COUNTER_SIZE) cnt();
      mkCounter#(fromInteger(lat)) the_cnt(cnt);

      // This rule fires when the tag at the head of the tags queue matches
      // its own number, and (by implicit condition) when a result is
      // available from the main server:
      rule respond (tags.first == i);
	 tags.deq;
	 let x <- ser.response.get();
	 ofifo.enq(x);
      endrule

      // The interface for each port -- note that requests are accepted only
      // when the count is non-zero.
      interface Put request;
	 method put(x) if (cnt.value > 0);
	    action
	       ser.request.put(x);
	       tags.enq(i);
	       cnt.down;
	    endaction
	 endmethod
      endinterface

      interface Get response;
	 method get();
	    actionvalue
	       let x = ofifo.first;
	       ofifo.deq;
	       cnt.up;
	       return (x);
	    endactionvalue
	 endmethod
      endinterface
   endmodule: mkPort

   // This loop instantiates the three ports, using the BSV array ps to keep
   // the three resulting interfaces.
   Server#(a,b) ps[3];
   for (Integer i = 0; i<3; i=i+1)
      begin
	 Server#(a,b) p();
	 mkPort#(fromInteger(i)) the_p(p);
	 ps[i] = p;
      end
   
   // The three interfaces in ps become the result interface:
   return (tuple3(ps[0], ps[1], ps[2]));
endmodule


   
