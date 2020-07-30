package Format3;

import Probe::*;
import FShow::*;
import Vector::*;

////////////////////////////////////////////////////////////////////////////////
/// Define some types ....
////////////////////////////////////////////////////////////////////////////////

typedef Vector#(3,Bool) VOB;
typedef Tuple2#(Bit#(2), Bit#(2)) TUP;

typedef enum {READ, WRITE, UNKNOWN}  OpCommand   deriving(Bounded, Bits, Eq);

typedef struct {OpCommand command;
		Bit#(8)   addr;
		Bit#(8)   data;
		Bit#(8)   length;
		Bool      lock;
		} Header deriving (Eq, Bits, Bounded);

typedef union tagged {Header  Descriptor;
		      Bit#(8) Data;
		      } Request deriving(Eq, Bits, Bounded);

////////////////////////////////////////////////////////////////////////////////
/// Define FShow instances for the ones that aren't already in FShow.bsv
////////////////////////////////////////////////////////////////////////////////

instance FShow#(OpCommand);
   function Fmt fshow (OpCommand label);
      case (label)
	 READ:    return fshow("READ ");
	 WRITE:   return fshow("WRITE");
	 UNKNOWN: return fshow("UNKNOWN");
      endcase
   endfunction
endinstance

instance FShow#(Header);
   function Fmt fshow (Header value);
      return ($format("<HEAD ")
	      +
	      fshow(value.command)
	      +
	      $format(" (%0d)", value.length)
	      +
	      $format(" A:%h",  value.addr)
	      +
	      $format(" D:%h>", value.data));
   endfunction
endinstance

instance FShow#(Request);
   function Fmt fshow (Request request);
      case (request) matches
	 tagged Descriptor .a:
	    return fshow(a);
	 tagged Data .a:
	    return $format("<DATA %h>", a);
      endcase
   endfunction
endinstance

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

module dbgProbe (Probe#(a))
   provisos(FShow#(a));

   Probe#(Bit#(640)) _probe <- mkProbe;

   method Action _write(a value);
      let ascii <- $swriteAV(fshow(value));
      _probe <= ascii;
   endmethod

endmodule

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////


(* synthesize *)
module sysFormat3 (Empty);
   
   Reg#(Bit#(32)) value <- mkReg(1234);
   Reg#(Bit#(16)) count <- mkReg(0);
   
   // Probes to send "fshow" strings to waves
   Probe#(VOB)     vob_probe <- dbgProbe;
   Probe#(TUP)     tup_probe <- dbgProbe;
   Probe#(Request) req_probe <- dbgProbe;
   
   rule every;
      // generate some values
      VOB v_of_bools  = unpack(truncate(count));
      TUP a_tuple     = unpack(truncate(count));
      Request request = unpack(truncate(value));
      
      // send signals to waves.
      vob_probe <= v_of_bools;
      tup_probe <= a_tuple;
      req_probe <= request;
      
      // show use with $display
      $display("  A Vector: ", fshow(v_of_bools));
      $display("   A Tuple: ", fshow(a_tuple));
      $display(" A Request: ", fshow(request));
      $display("----------------------------------");
      
      // update values
      value <= (value << 1) | {0, (value[31] ^ value[21] ^ value[1] ^ value[01])};
      count <= count + 1;
      if (count == 30) $finish;
   endrule
   
endmodule


endpackage