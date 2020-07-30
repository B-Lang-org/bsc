package BGetPut;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

import Connectable::*;
import SyncConnectable::*;
import FIFOF::*;
import Clocks::*;
import GetPut::*;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

interface BGet#(type a);
   method ActionValue#(a) get();
   method Action finish();
endinterface

interface BPut#(type a);
   method Action put (a value);
   method Bool done();
endinterface

function BGet#(a) fifofToBGet (FIFOF#(a) fifo);
   return (interface BGet
	      method ActionValue#(a) get();
		 let value = fifo.first;
		 return value;
	      endmethod
   
	      method Action finish ();
		 fifo.deq();
	      endmethod
	   endinterface);
endfunction

function BPut#(a) fifofToBPut (FIFOF#(a) fifo);
   return (interface BPut
	      method Action put (a value) if (!fifo.notEmpty);
		 fifo.enq(value);
	      endmethod
   
	      method Bool done();
		 return (!fifo.notEmpty);
	      endmethod
	   endinterface);
endfunction

instance Connectable#(BGet#(a), BPut#(a));
   module mkConnection#(BGet#(a) get_side, BPut#(a) put_side) (Empty);
      
      Reg#(Bool) blocked <- mkReg(False);
   
      rule bget_transfer (put_side.done && !blocked);
	 blocked <= True;
	 let x <- get_side.get;
	 put_side.put(x);
      endrule
      
      rule bget_finish (put_side.done && blocked);
	 blocked <= False;
	 get_side.finish();
      endrule

   endmodule
endinstance

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

instance Connectable#(BPut#(a), BGet#(a));
   module mkConnection#(BPut#(a) put_side, BGet#(a) get_side) (Empty);
      mkConnection(get_side, put_side);
   endmodule
endinstance

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

instance SyncConnectable#(BPut#(a), BGet#(a))
   provisos (Bits#(a, sa));
   module mkSyncConnection#(BPut#(a) put_side, BGet#(a) get_side) 
      (Clock put_clk, Reset put_reset, Clock get_clk, Reset get_reset, Empty ignore)
      provisos (Bits#(a, sa));
      
      Reg#(Bool) blocked <- mkReg(False, clocked_by(put_clk), reset_by(put_reset));
      Reg#(Bool) grabbed0 <- mkReg(False, clocked_by(get_clk), reset_by(get_reset));
   
      Reg#(a)    get_value <- mkSyncReg(?,     get_clk, get_reset, put_clk);
      Reg#(Bool) grabbed   <- mkSyncReg(False, get_clk, get_reset, put_clk);

      SyncPulseIfc finish0 <- mkSyncHandshake(put_clk, put_reset, get_clk);
      SyncPulseIfc finish1 <- mkSyncHandshake(get_clk, get_reset, put_clk);
   
      rule update_get (!grabbed0);
	 let value <- get_side.get;
	 grabbed <= True;
	 grabbed0 <= True;
	 get_value <= value;
      endrule
   
      rule bgp_transfer (put_side.done && !blocked && grabbed);
	 blocked <= True;
	 put_side.put(get_value);
      endrule
   
      rule bgp_transfer2 (put_side.done && blocked && grabbed);
	 finish0.send;
      endrule
      
      rule bgp_finish0 (finish0.pulse);
	 get_side.finish();
	 grabbed <= False;
	 grabbed0 <= False;
	 finish1.send;
      endrule
   
      rule bgp_finish1 (finish1.pulse);
	 blocked <= False;
      endrule
      
   endmodule
endinstance

instance SyncConnectable#(BGet#(a), BPut#(a))
   provisos (Bits#(a, sa));
   module mkSyncConnection#(BGet#(a) get_side, BPut#(a) put_side) 
      (Clock get_clk, Reset get_reset, Clock put_clk, Reset put_reset, Empty ignore)
      provisos (Bits#(a, sa));
      
      mkSyncConnection(put_side, get_side, put_clk, put_reset, get_clk, get_reset);
      
   endmodule
endinstance


////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

instance SyncConnectable#(Put#(a), Get#(a))
   provisos (Bits#(a, sa));
   module mkSyncConnection#(Put#(a) put_side, Get#(a) get_side) 
      (Clock put_clk, Reset put_reset, Clock get_clk, Reset get_reset, Empty ignore)
      provisos (Bits#(a, sa));
   
      SyncFIFOIfc#(a) fifo <- mkSyncFIFO(2, get_clk, get_reset, put_clk);

      rule get_value;
	 let value <- get_side.get;
	 fifo.enq(value);
      endrule
   
      rule put;
	 let value = fifo.first();
	 fifo.deq();
	 put_side.put(value);
      endrule
      
   endmodule
endinstance

instance SyncConnectable#(Get#(a), Put#(a))
   provisos (Bits#(a, sa));
   module mkSyncConnection#(Get#(a) get_side, Put#(a) put_side) 
      (Clock get_clk, Reset get_reset, Clock put_clk, Reset put_reset, Empty ignore)
      provisos (Bits#(a, sa));
      
      mkSyncConnection(put_side, get_side, put_clk, put_reset, get_clk, get_reset);
      
   endmodule
endinstance

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

module mkSynCConnection#(Put#(a) put_side, Get#(a) get_side) 
      (Clock put_clk, Reset put_reset, Clock get_clk, Reset get_reset, Empty ignore)
      provisos (Bits#(a, sa));
   
      SyncFIFOIfc#(a) fifo <- mkSyncFIFO(2, get_clk, get_reset, put_clk);

      rule get_value;
	 let value <- get_side.get;
	 fifo.enq(value);
      endrule
   
      rule put;
	 let value = fifo.first();
	 fifo.deq();
	 put_side.put(value);
      endrule

endmodule


module mkCrossConnectionFromCC#(BGet#(a) get_side, BPut#(a) put_side) 
   (Clock put_clk, Reset put_reset, Empty ignore)
   provisos (Bits#(a, sa));
      
   Reg#(Bool) blocked <- mkReg(False, clocked_by(put_clk), reset_by(put_reset));
   Reg#(Bool) grabbed0 <- mkReg(False);
   
   Reg#(a) get_value <- mkSyncRegFromCC(?, put_clk);
   Reg#(Bool) grabbed <- mkSyncRegFromCC(False, put_clk);
   
   SyncPulseIfc finish0 <- mkSyncHandshakeToCC(put_clk, put_reset);
   SyncPulseIfc finish1 <- mkSyncHandshakeFromCC(put_clk);
   
   rule update_get (!grabbed0);
//      $display("(%5d) Grabbing get value", $time);
      let value <- get_side.get;
      grabbed <= True;
      grabbed0 <= True;
      get_value <= value;
   endrule
   
   rule bgp_transfer (put_side.done && !blocked && grabbed);
//      $display("(%5d) Transfering get value", $time);
      blocked <= True;
      put_side.put(get_value);
   endrule
   
   rule bgp_transfer2 (put_side.done && blocked && grabbed);
//      $display("(%5d) SEND", $time);
      finish0.send;
   endrule
      
   rule bgp_finish0 (finish0.pulse);
//      $display("(%5d) Sending get finish", $time);
      get_side.finish();
      grabbed <= False;
      grabbed0 <= False;
      finish1.send;
   endrule
   
   rule bgp_finish1 (finish1.pulse);
//      $display("(%5d) Final reset", $time);
      blocked <= False;
   endrule

endmodule


module mkCrossConnectionToCC#(Get#(a) get_side, Put#(a) put_side) 
   (Clock get_clk, Reset get_reset, Empty ignore)
   provisos (Bits#(a, sa));
      
   SyncFIFOIfc#(a) fifo <- mkSyncFIFOToCC(2, get_clk, get_reset);

   rule get_value;
//      $display("(%5d) getting value", $time);
      let value <- get_side.get;
      fifo.enq(value);
   endrule
   
   rule put;
//      $display("(%5d) transfer value", $time);
      let value = fifo.first();
      fifo.deq();
      put_side.put(value);
   endrule

endmodule

endpackage