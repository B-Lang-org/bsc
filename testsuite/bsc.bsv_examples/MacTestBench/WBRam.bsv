package WBRam;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

import WBone::*;
import SimpleRam::*;
import GetPut::*;
import FIFO::*;
import Control::*;
import TbEnvConfigs::*;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

typedef SimpleRamIFC#(Bit#(32), Bit#(32)) WBRamIFC;

interface WBoneRamIFC;
   interface Control cntrl;
   interface WBoneOpTxRxIFC  channel;
   interface WBRamIFC        ram;
endinterface

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

module mkWBRam#(TbEnvConfigs parent) (WBoneRamIFC);

   FIFO#(WBoneOp) in_fifo  <- mkFIFO;
   FIFO#(WBoneOp) out_fifo <- mkFIFO;

   SimpleRamIFC#(Bit#(16), Bit#(32)) simple_ram <-mkSimpleRam;

   function Bit#(16) map_address (Bit#(32) address);
      return truncate(address - parent.txrx_bfr_base);
   endfunction

   rule process_wbone_op;


      let wbone_op = in_fifo.first();
      in_fifo.deq();
      
      case (wbone_op.kind())
	 WRITE:   action
		     let address = wbone_op.addr.data;
		     let data = wbone_op.data.data;
		     simple_ram.write(map_address(truncate(address)), truncate(data));
		     wbone_op.status = ACK;
		     out_fifo.enq(wbone_op);
		  endaction
	 READ:    action
		     let address = wbone_op.addr.data;
		     let value = simple_ram.read(map_address(truncate(address)));
		     wbone_op.data = BusData { data: {0, value}, tag: unpack(0) };
		     wbone_op.status = ACK;
		     out_fifo.enq(wbone_op);
		  endaction
	 default: action
		     wbone_op.status = ERR;
		     out_fifo.enq(wbone_op);
		  endaction
      endcase
      
   endrule

   interface Control cntrl;
      method Action init();

      endmethod
   endinterface

   interface WBoneOpTxRxIFC channel;
      interface Get tx;
	 method ActionValue#(WBoneOp) get;
	    let value = out_fifo.first();
	    out_fifo.deq();
            return value;
	 endmethod
      endinterface
      interface Put rx;
	 method Action put (x);
	    in_fifo.enq(x);
	 endmethod
      endinterface
   endinterface

   interface  WBRamIFC ram;
      method Bit#(32) read (Bit#(32) addr);
	 return simple_ram.read(map_address(addr));
      endmethod
      method Action write (Bit#(32) addr, Bit#(32) data);
	 simple_ram.write(map_address(addr), data);
      endmethod
   endinterface
   
endmodule

      
endpackage

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////
