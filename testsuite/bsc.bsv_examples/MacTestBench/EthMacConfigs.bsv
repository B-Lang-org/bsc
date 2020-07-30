package EthMacConfigs;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

import Util::*;
import EthFrame::*;
import FIFO::*;
import GetPut::*;
import Randomizeable::*;
import Mii::*;
import Mac::*;
import Control::*;

////////////////////////////////////////////////////////////////////////////////
/// Set Configuration Values
////////////////////////////////////////////////////////////////////////////////

typedef struct {
		MacAddress addr;
		Bool       promiscuous;
		Bit#(8)    rate;
		Bit#(32)   slot_time;
		Bit#(16)   ifg;
		Bit#(16)   ifg_part1;
		Bit#(8)    attempt_limit;
		Bit#(8)    backoff_limit;
		} EthMacConfigsStruct deriving (Bounded, Bits);

typedef Configs#(EthMacConfigsStruct) EthMacConfigs;


module mkEthMacConfigs (EthMacConfigs);

   Reg#(Bool) initialized <- mkReg(False);

   Randomize#(MacAddress) addr_gen <- mkRandomizer;

   Reg#(MacAddress) addr           <- mkRegU;
   Reg#(Bool)       promiscuous    <- mkReg(True);
   Reg#(Bit#(8))    rate           <- mkReg(100);
   Reg#(Bit#(32))   slot_time      <- mkReg(5120);
   Reg#(Bit#(16))   ifg            <- mkReg(960);
   Reg#(Bit#(16))   ifg_part1      <- mkReg(640);
   Reg#(Bit#(8))    attempt_limit  <- mkReg(16);
   Reg#(Bit#(8))    backoff_limit  <- mkReg(10);

   rule initialize_finish (!initialized);
      let addr_rand <- addr_gen.next();
      addr_rand[47:46] = 0;

      addr <= addr_rand;
      $display("MAC Address is: %h.%h.%h.%h.%h.%h",
	       addr_rand[47:40], addr_rand[39:32], addr_rand[31:24], addr_rand[23:16], addr_rand[15:8], addr_rand[7:0]);

      initialized <= True;
   endrule

   interface Control cntrl;
      method Action init ();
	 addr_gen.cntrl.init();
      endmethod
   endinterface
   
   method _read() if (initialized);
      return EthMacConfigsStruct {addr:          addr,
				  promiscuous:   promiscuous,
				  rate:          rate,
				  slot_time:     slot_time,
				  ifg:           ifg,
				  ifg_part1:     ifg_part1,
				  attempt_limit: attempt_limit,
				  backoff_limit: backoff_limit
				  };
   endmethod
   

endmodule

endpackage