package WBMaster;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

import Arbiter::*;
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

module mkWBMaster#(Integer id, ArbiterClient_IFC arbiter) (WBoneXActorIFC);

   WBMasterConfigs self <- mkWBMasterConfigs;

   FIFOF#(WBoneOp) in_fifo  <- mkFIFOF;
   FIFO#(WBoneOp) wait_fifo  <- mkLFIFO;
   FIFO#(WBoneOp) out_fifo <- mkFIFO;

   Reg#(Bit#(8)) count <- mkReg(0);

   Reg#(Bool) response <- mkReg(False);

   WBoneZBusDualIFC buffer <-  mkWBoneZBusBuffer;
   
   rule request_grant (in_fifo.notEmpty && !response && !buffer.clientIFC.stb.get());
      arbiter.request;
   endrule

   rule process_wbone_op_start (arbiter.grant && !response && !buffer.clientIFC.stb.get());
      let wbone_op = in_fifo.first();
      wait_fifo.enq(wbone_op);
      in_fifo.deq();
   endrule

   rule process_wbone_op (!response);
      
      let wbone_op = wait_fifo.first();
      count <= count + 1;
      case (wbone_op.kind())
	 WRITE:   action
		     initiate_write(buffer.clientIFC, wbone_op);
		  endaction
	 READ:    action
		     initiate_read(buffer.clientIFC, wbone_op);
		  endaction
	 default: action
		  endaction
      endcase
      
   endrule

   rule process_response (response_detected(buffer.clientIFC) && !response);

      response <= True;

      let wbone_op = wait_fifo.first();
      wait_fifo.deq();

      let response_wbone_op = createWBoneOp(buffer.clientIFC);

      wbone_op.status = response_wbone_op.status;
      wbone_op.data = response_wbone_op.data;

      out_fifo.enq(wbone_op);
      
   endrule

   rule flip (response);
      response <= False;
      count <= 0;
   endrule
      
   rule timeout (!response_detected(buffer.clientIFC) && (count > self.max_n_wss));
      
      let wbone_op = wait_fifo.first();
      wait_fifo.deq();

      wbone_op.status = TIMEOUT;
      
      $display("Timeout! (%5d)", $time);
      
      out_fifo.enq(wbone_op);
   endrule

   interface Control cntrl;
      method Action init();
	 self.cntrl.init();
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

function Bool response_detected (WBoneZBusClientIFC ifc);

   return (ifc.ack.get() || ifc.err.get() || ifc.rty.get());
endfunction

   
////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

function Action initiate_write (WBoneZBusClientIFC ifc, WBoneOp op);
   action
      ifc.adr.drive(op.addr);
      ifc.dato.drive(op.data);
      ifc.we.drive(True);
      ifc.sel.drive(op.sel);
      ifc.cyc.drive(BusCycle{ data: True, tag: op.tgc});
      ifc.lock.drive(op.lock);
      ifc.stb.drive(True);
   endaction
endfunction

function Action initiate_read (WBoneZBusClientIFC ifc, WBoneOp op);
   action
      ifc.adr.drive(op.addr);
      ifc.we.drive(False);
      ifc.sel.drive(op.sel);
      ifc.cyc.drive(BusCycle{ data: True, tag: op.tgc});
      ifc.lock.drive(op.lock);
      ifc.stb.drive(True);
   endaction
endfunction

endpackage

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

