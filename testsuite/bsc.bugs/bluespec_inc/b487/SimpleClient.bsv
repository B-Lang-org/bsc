////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

package SimpleClient;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

import ZBusBuffer::*;

typedef Bit#(16) BAddr;
typedef Bit#(32) BData;

// typedef enum {Idle, Read, Write} BCtl deriving (Eq, Bits);

typedef Bit#(3) BCtl;

BCtl idle;
BCtl read;
BCtl write;

idle = 'b000;
read = 'b100;
write ='b010;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

// A tuple is not a valid module interface, so expose the three ZBus sides
// through a named interface instead.
interface ClientIFC;
   interface ZBusIFC#(BCtl)  ctl;
   interface ZBusIFC#(BAddr) addr;
   interface ZBusIFC#(BData) data;
endinterface

(* synthesize *)
module mkSimpleClient (ClientIFC);

   Reg#(BAddr)       self();
   mkReg#(0)         reg_self(self);

   Reg#(BData)       dta();
   mkReg#(0)         reg_dta(dta);

   ZBusIFC#(BCtl) ctl_ifc();
   mkZBusBuffer inst_ctl_ifc(ctl_ifc);

   ZBusIFC#(BAddr) addr_ifc();
   mkZBusBuffer inst_addr_ifc(addr_ifc);

   ZBusIFC#(BData) data_ifc();
   mkZBusBuffer inst_data_ifc(data_ifc);

   rule read (ctl_ifc.fromBusValid() &&
	      addr_ifc.fromBusValid() &&
	      (ctl_ifc.fromBusValue() == read) &&
	      (self == addr_ifc.fromBusValue()));
      action
	 data_ifc.toBusSample(dta, True);
       endaction
   endrule

   rule write (ctl_ifc.fromBusValid() &&
	       addr_ifc.fromBusValid() &&
	       data_ifc.fromBusValid() &&
	      (ctl_ifc.fromBusValue() == write) &&
	      (self == addr_ifc.fromBusValue()));
       action
	  dta <= data_ifc.fromBusValue();
       endaction
   endrule

   interface ctl  = ctl_ifc;
   interface addr = addr_ifc;
   interface data = data_ifc;

endmodule

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

endpackage

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

