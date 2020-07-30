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

(* synthesize *)
module mkSimpleClient (Tuple3#(ZBusIFC#(BCtl),ZBusIFC#(BAddr),ZBusIFC#(BData)));

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

   return tuple3(ctl_ifc, addr_ifc, data_ifc);

endmodule

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

endpackage

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

