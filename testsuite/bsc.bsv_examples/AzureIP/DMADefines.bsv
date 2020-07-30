package DMADefines;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

import CBus::*;
import Randomizable::*;
import TLM::*;

`include "TLM.defines"

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

typedef 1 NumChannels;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

// Values currently selected so Transfer descriptor will fit in 32 bits.
typedef TransferDescriptor#(`TLM_STD_TYPES)  TransferDescriptorStd;
typedef Bit#(11) DescAddr;
typedef Bit#(6)  DescLen;

typedef struct {DescAddr source;
		DescAddr dest;
		DescLen  length;
		} TransferDescriptor#(`TLM_TYPE_PRMS) deriving (Eq, Bits, Bounded);


instance Randomizable#(TransferDescriptor#(`TLM_TYPES));

   module mkRandomizer (Randomize#(TransferDescriptor#(`TLM_TYPES)));

      Randomize#(DescLen)  length_gen <- mkGenericRandomizer;
      Randomize#(Bit#(9))  dest_gen   <- mkGenericRandomizer;
      Randomize#(Bit#(9))  source_gen <- mkGenericRandomizer;

      interface Control cntrl;
	 method Action init();
	    source_gen.cntrl.init();
	    dest_gen.cntrl.init();
	    length_gen.cntrl.init();
	 endmethod
      endinterface

      method ActionValue#(TransferDescriptor#(`TLM_TYPES)) next ();

	 let descriptor = unpack(0);

	 let source <- source_gen.next;
	 let dest   <- dest_gen.next;
	 let length <- length_gen.next;

	 descriptor.source = {source, 0};
	 descriptor.dest   = {dest,   0};
	 descriptor.length = length;

	 return descriptor;
      endmethod

   endmodule

endinstance

////////////////////////////////////////////////////////////////////////////////
/// Configuration Register Types
////////////////////////////////////////////////////////////////////////////////

typedef 12 DCBusAddrWidth;
typedef 32 DCBusDataWidth;

typedef CBus#(DCBusAddrWidth, 32) DCBus;
typedef ModWithCBus#(DCBusAddrWidth, 32, i) DModWithCBus#(type i);

typedef CRAddr#(DCBusAddrWidth,DCBusDataWidth) DCAddr;

////////////////////////////////////////////////////////////////////////////////
/// Configuration Register Locations
////////////////////////////////////////////////////////////////////////////////

DCAddr statusAddr   = DCAddr {a: 12'h000, o:  0};

////////////////////////////////////////////////////////////////////////////////
/// Configuration Register Locations For Each Channel
////////////////////////////////////////////////////////////////////////////////

DCAddr descriptorAddrBase = DCAddr {a: 12'h100, o:  0};
DCAddr activeAddrBase     = DCAddr {a: 12'h104, o:  0};

function DCAddr calculateDCAddrForChannel(DCAddr base, Bit#(12) channel);
   let delta = DCAddr { a: (channel * 12'h020), o: 0};
   let addr = base + delta;
   return addr;
endfunction

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////


endpackage
