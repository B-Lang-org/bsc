import GetPut::*;
import CGetPut::*;
import FIFO::*;
import LFSR::*;
import RandGlobalC::*;

// The first part of this file defines a random number generator.  The
// algorithm uses the library LFSR (Linear Feedback Shift Register) package.
// This produces reasonable pseudo-random numbers for many purposes (though
// not good enough for cryptography).  The package defines several versions of
// mkLFSR, with different widths of output.  We want 6-bit random numbers, so
// we will use the 16-bit version, and take the most significant six bits.

// The interface for LFSR is defined as follows:
//
// interface LFSR #(type a);
//     method Action seed(a x1);
//     method a value();
//     method Action next();
// endinterface: LFSR
//
// The seed method must be called first, to prime the algorithm.  Then values
// may be read using the value method, and the algorithm stepped on to the
// next value by the next method.

// The interface for the random number generator is also parameterized on bit
// length.  It is a "get" interface, defined in the GetPut package.

typedef Get#(Bit#(n)) RandI#(type n);

// This next module is the random number generator itself

module mkRn_6(RandI#(6));
  // First we instantiate the LFSR module
  LFSR#(Bit#(16)) lfsr();
  mkLFSR_16 thelfsr(lfsr);

  // Next comes a FIFO for storing the results until needed
  FIFO#(Bit#(6)) fi();
  mkFIFO thefi(fi);

  // A boolean flag for ensuring that we first seed the LFSR module
  Reg#(Bool) starting();
  mkReg#(True) thestarting(starting);

  // This rule fires first, and sends a suitable seed to the module.
  rule start
  (starting);
      starting <= False;
      (lfsr.seed)('h11);
  endrule: start

  // After that, the following rule runs as often as it can, retrieving
  // results from the LFSR module and enqueing them on the FIFO.
  rule run
  (not(starting));
      (fi.enq)(lfsr.value[10:5]);
      lfsr.next;
  endrule: run

  // The interface for mkRn_6 is a Get interface.  We can produce this from a
  // FIFO using the fifoToGet function.  We therefore don't need to define any
  // new methods explicitly in this module: we can simply return the produced
  // Get interface as the "result" of this module instantiation.
  return fifoToGet(fi);
endmodule


(* synthesize *)
module mkSplitter(GenPair);
  RandI#(6) rn();
  mkRn_6 the_rn(rn);

  CGetPut#(4, Bit#(6)) rn1GP();
  mkCGetPut the_rn1GP(rn1GP);
  CGetPut#(4, Bit#(6)) rn2GP();
  mkCGetPut the_rn2GP(rn2GP);

  rule fill_rn1F;
	  action
            Bit#(6) x;
	    x <- rn.get;
	    (rn1GP.snd.put)(x);
	  endaction
  endrule

  rule fill_rn2F;
	  action
            Bit#(6) x;
	    x <- rn.get;
	    (rn2GP.snd.put)(x);
	  endaction
  endrule

  return (tuple2(rn1GP.fst,rn2GP.fst));

endmodule: mkSplitter


