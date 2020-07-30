package HammingQ;

/* --------------------------------------------------
                                 p q r
Hamming numbers are of the form 2 3 5 , where p,q and r are natural
numbers (including 0).  This package displays the infinite sequence
of these numbers, in ascending order, with no duplicates.  The package
is deemed to work if it produces, say, the first 100 elements of this
sequence. 

--------------------------------------------------
 
We note the following facts about the sequence:
(i)   1 is an element (p,q,r are all 0), and moreover it's the first
one.
(ii)  If  n  is an element of the sequence, so is  2n.
(iii) If  n  is an element, so is  3n.
(iv)  If  n  is an element, so is  5n.
(v)   These are all the elements.

Our design will accordingly do the following:
(i)   Place 1 on a "channel", which will convey the sequence;
(ii)  produce channels carrying the values on this channel all x2, x3
and x5, respectively;
(iii) use a module mkMerge, which has an interface with two input
channels, and one output channel, expecting numbers to come in on the
two input channels in ascending order, and will output the merged
sequence, also in ascending order, without duplicates;
(iv)  feed the merged sequence, formed from the scaled channels, back
to the original channel.

 -------------------------------------------------- */

// We import the library packages we shall need.

import FIFO::*;
import GetPut::*;
import Connectable::*;

// It's convenient to give a name to the type of numbers we use
// throughout the design: a change in this is then a one-line change.

typedef Int#(32) Num;

// Our interfaces into modules (i.e. into which users of the module can
// "put" numbers, will be Put interfaces, and the interfaces out of
// which users can "get" numbers, will be Get interfaces; it's
// convenient to define types for them too.

typedef Get#(Num) Gt;
typedef Put#(Num) Pt;

// We next define the mkMerge module described above.  Its interface
// provides two inputs and one output; each of these is a
// sub-interface:

interface MergeI;
   interface Gt oput;
   interface Pt iput1;
   interface Pt iput2;
endinterface: MergeI

module mkMerge(MergeI);
   // We first provide an input fifo for each of the input channels:
   FIFO#(Num) ififo1();
   mkFIFO the_ififo1(ififo1);
   
   FIFO#(Num) ififo2();
   mkFIFO the_ififo2(ififo2);

   // An output fifo for the output channel:
   FIFO#(Num) ofifo();
   mkFIFO the_ofifo(ofifo);

   // TASK: complete the definition of this module (HINT: rules?):

   // ...
   
   // We use library functions (from the GetPut package) to produce the
   // input and output interfaces from the appropriate fifo.  fifoToPut
   // produces a Put interface, whose method enqueues its parameter
   // value on the Fifo; similarly the Get interface dequeues the Fifo,
   // returning its first element.
   interface iput1 = fifoToPut(ififo1);
   interface iput2 = fifoToPut(ififo2);
   interface oput = fifoToGet(ofifo);
endmodule: mkMerge

// --------------------------------------------------

// The next function takes four Put interfaces as parameters, and
// produces a single Put interface which sends each value it receives
// to all four of them.  NOTE: this is treating interfaces as
// first-class objects, allowing them to be parameters and results of
// functions.

function Pt fanout (Pt p1, Pt p2, Pt p3, Pt p4);
   return
     (interface Put;
	 method put(x);
	    action
	       p1.put(x);
	       p2.put(x);
	       p3.put(x);
	       p4.put(x);
	    endaction
	 endmethod
      endinterface);
endfunction: fanout   

// The next function takes a Put interface  p  as parameter, and also a
// number  i.  It produces a Put interface as result, which send  i
// times each number it receives to its parameter interface.

function Pt times (Num i, Pt p);
   // TASK: write the body of this function.
   
   // ...
   return (?);
endfunction: times
   
// --------------------------------------------------

// Our final auxiliary module is one which provides a Put interface,
// and displays each number it receives on it.
module mkSink(Pt);
   method put(x);
      action
	 $display(x);
      endaction
   endmethod
endmodule
      
// --------------------------------------------------


// Finally comes the "top-level" module, which is the one to be
// synthesized.
(* synthesize *)
module mkHamming(Empty);
   // We instantiate the sink:
   Pt sink();
   mkSink the_sink(sink);

   // We shall need two merge modules:
   MergeI m1();
   mkMerge the_m1(m1);
   MergeI m2();
   mkMerge the_m2(m2);

   // TASK: complete the following definitions:
   Pt double_path = ?;
   Pt triple_path = ?;
   Pt quint_path  = ?;

   // The sequence, as it is computed, must be sent to the sink, and also to
   // the channels which compute later elements:
   Pt hamming_seq = fanout(sink, double_path, triple_path, quint_path);

   // Get interfaces and Put interfaces may be connected together:
   mkConnection(m2.oput, hamming_seq);
   // TASK: supply any further connections which may be needed:
   // ...

   // To start things off we need a rule to inject the "1", and a
   // register to ensure it's invoked only once:
   Reg#(Bool) starting();
   mkReg#(True) the_starting(starting);
   rule starter (starting);
      hamming_seq.put(1);
      starting <= False;
   endrule

endmodule: mkHamming

/* --------------------------------------------------

When you complete and simulate this package, you will find that it
almost works.  Try and work out what the problem is, and think of how
it could be fixed.  HINT: consider using the module mkGPSizedFifo, from
the GetPut package, which instantiates a FIFO of sized specified by a
parameter, and provides a pair of interfaces (a Get and a Put) to it.
It may be used as follows:
 
   // Instantiate the interface (a pair of sub-interfaces):
   Tuple2#(Gt,Pt) sf();
   // Instantiate the fifo:
   mkGPSizedFIFO#(100) the_sf(sf);
   // Use pattern-matching to give names to the two sub-interfaces:
   match {fg, fp} = sf;

This package produces a self-contained module, with an "Empty"
interface.  You might consider revising the architecture so that
mkHamming has an interface which produces numbers, taking mkSink out of
mkHamming and promoting it to separate testbench status, and defining a
new top-level module, mkTopLevel (which will again have an Empty
interface) to connect them together and run the result.  HINT: it's
easiest if you give mkHamming an output fifo.
 
 -------------------------------------------------- */
      
endpackage: HammingQ
