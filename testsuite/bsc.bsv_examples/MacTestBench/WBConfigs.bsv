package WBConfigs;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

import WBone::*;
import Util::*;
import Control::*;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

typedef struct {
		BusAddr min_addr;
		BusAddr max_addr;
		Bit#(8) max_n_wss;
		} WBMasterConfigsStruct;


typedef Configs#(WBMasterConfigsStruct) WBMasterConfigs;

module mkWBMasterConfigs (WBMasterConfigs);

   Reg#(Bool) initialized <- mkReg(False);

   interface Control cntrl;
      method Action init ();
	 initialized <= True;
      endmethod
   endinterface
   
   method _read() if (initialized);
      let min_addr = BusAddr { data: ('h7ff + 1), tag: unpack(0) };
      let max_addr = BusAddr { data:       50000, tag: unpack(0) };
      let max_n_wss = 10;
      return WBMasterConfigsStruct {
				    min_addr:  min_addr,
				    max_addr:  max_addr,
				    max_n_wss: max_n_wss
				    };
   endmethod
   

endmodule

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

typedef struct {
		BusAddr min_addr;
		BusAddr max_addr;
		Bit#(8) max_n_wss;
		} WBSlaveConfigsStruct;


typedef Configs#(WBSlaveConfigsStruct) WBSlaveConfigs;

module mkWBSlaveConfigs (WBSlaveConfigs);

   Reg#(Bool) initialized <- mkReg(False);

   interface Control cntrl;
      method Action init ();
	 initialized <= True;
      endmethod
   endinterface
   
   method _read() if (initialized);
      let min_addr = BusAddr { data: ('h7ff + 1), tag: unpack(0) };
      let max_addr = BusAddr { data: 'hFFFF_FFFF, tag: unpack(0) };
      let max_n_wss = 10;
      return WBSlaveConfigsStruct {
				   min_addr:  min_addr,
				   max_addr:  max_addr,
				   max_n_wss: max_n_wss
				   };
   endmethod
   

endmodule

endpackage

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

