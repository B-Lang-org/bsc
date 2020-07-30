package WBSlave2;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

import Util::*;
import Control::*;
import WBone::*;
import GetPut::*;
import FIFO::*;
import FIFOF::*;
import ZBus::*;
import WBConfigs::*;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

module mkWBSlave2#(Integer min_addr,
		   Integer max_addr
		   ) (WBoneXActorIFC);

   Reg#(Bool) monitoring <- mkReg(True);

   FIFOF#(WBoneOp) in_fifo  <- mkFIFOF;
   FIFO#(WBoneOp) out_fifo <- mkFIFO;

   WBoneZBusDualIFC buffer <-  mkWBoneZBusBuffer;

   rule monitor_bus (monitoring && buffer.clientIFC.stb.get());

      let tagged_addr = buffer.clientIFC.adr.get();
      let addr = tagged_addr.data;

      if ((fromInteger(min_addr) <= addr) && (addr <= fromInteger(max_addr)))
	 begin
	    monitoring <= False;
	    let wbone_op = createWBoneOp(buffer.clientIFC);
//	    $display("(%5d) slave (%0d) gets request", $time, min_addr);
//	    displayWBoneOp(wbone_op);
	    out_fifo.enq(wbone_op);
	 end

   endrule

   rule respond (!monitoring && in_fifo.notEmpty());
      let wbone_op = in_fifo.first();
      in_fifo.deq();
      monitoring <= True;
      send_response(buffer.clientIFC, wbone_op);
   endrule

   rule hold_bus (!monitoring && !in_fifo.notEmpty());
      buffer.clientIFC.ack.drive(False);
      buffer.clientIFC.err.drive(False);
      buffer.clientIFC.rty.drive(False);
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

   interface bus = buffer.busIFC();

endmodule

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

function Action send_response (WBoneZBusClientIFC ifc, WBoneOp op);
   action
      if (op.status == ERR)
	 begin
	    ifc.ack.drive(False);
	    ifc.err.drive(True);
	    ifc.rty.drive(False);
	 end
      else if (op.kind == READ)
	 begin
	    ifc.ack.drive(True);
	    ifc.err.drive(False);
	    ifc.rty.drive(False);
	    ifc.dati.drive(op.data);
	 end
      else if (op.kind == WRITE)
      	 begin
	    ifc.ack.drive(True);
	    ifc.err.drive(False);
	    ifc.rty.drive(False);
	 end
      else
	 begin
	    ifc.ack.drive(False);
	    ifc.err.drive(True);
	    ifc.rty.drive(False);
	 end
   endaction
endfunction

endpackage

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////
