// Crossbar switch, butterfly topology

package XBar;

import FIFO :: *;
import FIFOF :: *;
import List :: *;
import GetPut :: *;

// =====================================
// Basic building block: a 2-to-1 merge

interface Merge2x1 #(type t);
   interface Put#(t) iport0;
   interface Put#(t) iport1;
   interface Get#(t) oport;
endinterface

// ----------------
// An implementation of Merge2x1
// Arbitration on two inputs:
//   static unspecified priority

module mkMerge2x1_static (Merge2x1#(t))
   provisos (Bits#(t, wt));

   FIFO#(t) f <- mkFIFO;

   interface Put iport0;
      method Action put (x);
         f.enq (x);
      endmethod
   endinterface
   interface Put iport1;
      method Action put (x);
         f.enq (x);
      endmethod
   endinterface
   interface Get oport;
      method ActionValue#(t) get;
         f.deq;
         return f.first;
      endmethod
   endinterface
endmodule: mkMerge2x1_static

// ----------------
// An implementation of Merge2x1
// Arbitration on two inputs: LRU (fair)

module mkMerge2x1_lru (Merge2x1#(t))
   provisos (Bits#(t, wt));

   FIFOF#(t) fi0 <- mkFIFOF;
   FIFOF#(t) fi1 <- mkFIFOF;
   FIFOF#(t) fo  <- mkFIFOF;

   Reg#(Bool) fi0HasPrio <- mkReg (True);

   rule fi0_is_empty (! fi0.notEmpty);
      let x = fi1.first;
      fi1.deq;
      fo.enq (x);
      fi0HasPrio <= True;
   endrule

   rule fi1_is_empty (! fi1.notEmpty);
      let x = fi0.first;
      fi0.deq;
      fo.enq (x);
      fi0HasPrio <= False;
   endrule

   rule both_have_data
    (fi0.notEmpty && fi1.notEmpty);
      FIFOF#(t) fi =
            ((fi0HasPrio) ? fi0 : fi1);
      let x = fi.first;
      fi.deq;
      fo.enq (x);
      fi0HasPrio <= ! fi0HasPrio;
   endrule

   interface Put iport0;
      method Action put (x);
         fi0.enq (x);
      endmethod
   endinterface
   interface Put iport1;
      method Action put (x);
         fi1.enq (x);
      endmethod
   endinterface
   interface Get oport;
      method ActionValue#(t) get;
         fo.deq;
         return fo.first;
      endmethod
   endinterface
endmodule: mkMerge2x1_lru

// =====================================

// THE XBar MODULE
// ----------------

// The XBar module interface

interface XBar #(type t);
   interface List#(Put#(t))  input_ports;
   interface List#(Get#(t))  output_ports;
endinterface

// ----------------
// The routing function: decides whether
// the packet goes straight through, or
// gets "flipped" to the opposite side

function Bool flipCheck (Bit #(32) dst,
			 Bit #(32) src,
			 Integer logn);
    return (dst[fromInteger(logn-1)] !=
	     src [fromInteger(logn-1)]);
endfunction: flipCheck

// ----------------
// The XBar module constructor

module mkXBar #(
   Integer logn,
   function Bit #(32) destinationOf (t x),
   module #(Merge2x1 #(t)) mkMerge2x1
		) (XBar #(t))
      provisos (Bits#(t, wt));

   List#(Put#(t)) iports;
   List#(Get#(t)) oports;

   // ---- BASE CASE (n = 1 = 2^0)
   if (logn == 0) begin
      FIFO#(t) f <- mkFIFO;
      iports = cons (fifoToPut (f), nil);
      oports = cons (fifoToGet (f), nil);
   end

   // ---- RECURSIVE CASE
   //       (n = 2^logn, logn > 0)
   else begin
      Integer n     = exp(2, logn);
      Integer nHalf = div (n, 2);

      // Recursively create two
      // switches of half size
      XBar#(t) upper <- mkXBar (logn-1,
	       destinationOf, mkMerge2x1);
      XBar#(t) lower <- mkXBar (logn-1,
	       destinationOf, mkMerge2x1);

      // input ports are just the input
      //  ports of upper and lower halves
      iports = append(upper.input_ports,
		      lower.input_ports);

      // intermediate ports are output
      //  ports of upper and lower halves
      List#(Get#(t)) oports_mid =
               append(upper.output_ports,
		      lower.output_ports);

      // Create new column of n 2x1 merges
      List#(Merge2x1#(t)) merges
            <- replicateM (n, mkMerge2x1);

      // output ports are just the
      // output ports of the new merges
      oports = nil;
      for (Integer j = n-1;
	             j >= 0; j = j - 1)
        oports =
          cons (merges [j].oport, oports);

      // Routing from each intermediate
      // oport to new column
      for (Integer j = 0;
                     j < n; j = j + 1)
      begin
        rule route;
          let x <- oports_mid [j].get;
          Bool flip = flipCheck
	     (destinationOf (x),
	         fromInteger (j), logn);
          let jFlipped = ((j < nHalf) ?
			  j + nHalf : j
			  - nHalf);
	  if (! flip)
             merges [j].iport0.put (x);
          else
             merges
             [jFlipped].iport1.put (x);
        endrule
     end
  end

  interface input_ports  = iports;
  interface output_ports = oports;
endmodule: mkXBar

endpackage: XBar
