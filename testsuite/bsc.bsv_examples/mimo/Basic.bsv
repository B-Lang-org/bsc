import MIMO::*;
import StmtFSM::*;
import Vector::*;
import DefaultValue::*;

// :enq (1, some, all)
// :deq (1, some, all)
// :enq (1)
//  deq (1, some, all)
// :enq (some)
//  deq (1, some, all)
// :enq (rest)
//  deq (1, some)
// :enq/deq/clear

(* synthesize *)
module sysBasic();
   MIMOConfiguration cfg = defaultValue;
   MIMOConfiguration cfg2 = defaultValue;
   cfg.bram_based = True;
   
   MIMO#(16,16,48,Bit#(8)) dut <- mkMIMO(cfg);
   MIMO#(16,16,48,Bit#(8)) dut2 <- mkMIMO(cfg2);
   
   mkAutoFSM(seq
		delay(10);
		// fill in with some information
		dut.enq(1, unpack('h01));
		dut.enq(2, unpack('h0302));
		dut.enq(3, unpack('h060504));
		dut.enq(4, unpack('h0A090807));
		dut.enq(5, unpack('h0F0E0D0C0B));
		dut.enq(6, unpack('h151413121110));
		dut.enq(7, unpack('h1C1B1A19181716));
		dut.enq(8, unpack('h24232221201F1E1D));
      
		// enqueue one item
		action
		   $display("%b %b %b %b %d %x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x", dut.enqReady(), dut.deqReady(), dut.enqReadyN(1), dut.deqReadyN(0), dut.count(), 
		      dut.first()[15], dut.first()[14], dut.first()[13], dut.first()[12], 
		      dut.first()[11], dut.first()[10], dut.first()[9], dut.first()[8], 
		      dut.first()[7], dut.first()[6], dut.first()[5], dut.first()[4], 
		      dut.first()[3], dut.first()[2], dut.first()[1], dut.first()[0]);
		   dut.enq(1, unpack('h25));
		endaction
      
		// enqueue some items (to fill mimo)
		action
		   $display("%b %b %b %b %d %x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x", dut.enqReady(), dut.deqReady(), dut.enqReadyN(11), dut.deqReadyN(0), dut.count(), 
		      dut.first()[15], dut.first()[14], dut.first()[13], dut.first()[12], 
		      dut.first()[11], dut.first()[10], dut.first()[9], dut.first()[8], 
		      dut.first()[7], dut.first()[6], dut.first()[5], dut.first()[4], 
		      dut.first()[3], dut.first()[2], dut.first()[1], dut.first()[0]);
		   dut.enq(11, unpack('h302F2E2D2C2B2A29282726));
		endaction
      
		// full mimo (try removing one)
		action
		   $display("%b %b %b %b %d %x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x", dut.enqReady(), dut.deqReady(), dut.enqReadyN(0), dut.deqReadyN(1), dut.count(), 
		      dut.first()[15], dut.first()[14], dut.first()[13], dut.first()[12], 
		      dut.first()[11], dut.first()[10], dut.first()[9], dut.first()[8], 
		      dut.first()[7], dut.first()[6], dut.first()[5], dut.first()[4], 
		      dut.first()[3], dut.first()[2], dut.first()[1], dut.first()[0]);
		   dut.deq(1);
		endaction
      
		// simultaneous enq/deq
		action
		   $display("%b %b %b %b %d %x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x", dut.enqReady(), dut.deqReady(), dut.enqReadyN(2), dut.deqReadyN(1), dut.count(), 
		      dut.first()[15], dut.first()[14], dut.first()[13], dut.first()[12], 
		      dut.first()[11], dut.first()[10], dut.first()[9], dut.first()[8], 
		      dut.first()[7], dut.first()[6], dut.first()[5], dut.first()[4], 
		      dut.first()[3], dut.first()[2], dut.first()[1], dut.first()[0]);
		   dut.enq(2, unpack('h3231));
		   dut.deq(1);
		endaction
      
		// check full status
		action
		   $display("F: %b %b %b %b %d %x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x", dut.enqReady(), dut.deqReady(), dut.enqReadyN(1), dut.deqReadyN(1), dut.count(), 
		      dut.first()[15], dut.first()[14], dut.first()[13], dut.first()[12], 
		      dut.first()[11], dut.first()[10], dut.first()[9], dut.first()[8], 
		      dut.first()[7], dut.first()[6], dut.first()[5], dut.first()[4], 
		      dut.first()[3], dut.first()[2], dut.first()[1], dut.first()[0]);
		endaction
      
		// dequeue max amount until empty
		action
		   $display("%b %b %b %b %d %x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x", dut.enqReady(), dut.deqReady(), dut.enqReadyN(0), dut.deqReadyN(16), dut.count(), 
		      dut.first()[15], dut.first()[14], dut.first()[13], dut.first()[12], 
		      dut.first()[11], dut.first()[10], dut.first()[9], dut.first()[8], 
		      dut.first()[7], dut.first()[6], dut.first()[5], dut.first()[4], 
		      dut.first()[3], dut.first()[2], dut.first()[1], dut.first()[0]);
		   dut.deq(16);
		endaction
      
		// dequeue max amount until empty
		action
		   $display("%b %b %b %b %d %x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x", dut.enqReady(), dut.deqReady(), dut.enqReadyN(0), dut.deqReadyN(16), dut.count(), 
		      dut.first()[15], dut.first()[14], dut.first()[13], dut.first()[12], 
		      dut.first()[11], dut.first()[10], dut.first()[9], dut.first()[8], 
		      dut.first()[7], dut.first()[6], dut.first()[5], dut.first()[4], 
		      dut.first()[3], dut.first()[2], dut.first()[1], dut.first()[0]);
		   dut.deq(16);
		endaction
      
		// dequeue max amount until empty
		action
		   $display("%b %b %b %b %d %x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x", dut.enqReady(), dut.deqReady(), dut.enqReadyN(0), dut.deqReadyN(16), dut.count(), 
		      dut.first()[15], dut.first()[14], dut.first()[13], dut.first()[12], 
		      dut.first()[11], dut.first()[10], dut.first()[9], dut.first()[8], 
		      dut.first()[7], dut.first()[6], dut.first()[5], dut.first()[4], 
		      dut.first()[3], dut.first()[2], dut.first()[1], dut.first()[0]);
		   dut.deq(16);
		endaction
      
		// verify empty status
		action
		   $display("E: %b %b %b %b %d ", dut.enqReady(), dut.deqReady(), dut.enqReadyN(1), dut.deqReadyN(16), dut.count());
		endaction
      
		// action clear/enqueue in same cycle
		action
		   dut.enq(13, unpack('h3F3E3D3C3B3A39383736353433));
		   dut.clear();
		endaction

		// verify empty status
		action
		   $display("E: %b %b %b %b %d ", dut.enqReady(), dut.deqReady(), dut.enqReadyN(1), dut.deqReadyN(16), dut.count());
		endaction
      
		// action clear/dequeue in same cycle
		dut.enq(14, unpack('h4D4C4B4A49484746454443424140));
		action
		   dut.deq(14);
		   dut.clear();
		endaction

		// verify empty status
		action
		   $display("E: %b %b %b %b %d ", dut.enqReady(), dut.deqReady(), dut.enqReadyN(1), dut.deqReadyN(16), dut.count());
		endaction

		// action clear/enqueue/dequeue in same cycle
		dut.enq(15, unpack('h5C5B5A595857565554535251504F4E));
		action
		   dut.deq(15);
		   dut.enq(16, unpack('h6C6B6A696867666564636261605F5E5D));
		   dut.clear();
		endaction

		// verify empty status
		action
		   $display("E: %b %b %b %b %d ", dut.enqReady(), dut.deqReady(), dut.enqReadyN(1), dut.deqReadyN(16), dut.count());
		endaction
      
		delay(10);
		// fill in with some information
		dut2.enq(1, unpack('h01));
		dut2.enq(2, unpack('h0302));
		dut2.enq(3, unpack('h060504));
		dut2.enq(4, unpack('h0A090807));
		dut2.enq(5, unpack('h0F0E0D0C0B));
		dut2.enq(6, unpack('h151413121110));
		dut2.enq(7, unpack('h1C1B1A19181716));
		dut2.enq(8, unpack('h24232221201F1E1D));
      
		// enqueue one item
		action
		   $display("%b %b %b %b %d %x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x", dut2.enqReady(), dut2.deqReady(), dut2.enqReadyN(1), dut2.deqReadyN(0), dut2.count(), 
		      dut2.first()[15], dut2.first()[14], dut2.first()[13], dut2.first()[12], 
		      dut2.first()[11], dut2.first()[10], dut2.first()[9], dut2.first()[8], 
		      dut2.first()[7], dut2.first()[6], dut2.first()[5], dut2.first()[4], 
		      dut2.first()[3], dut2.first()[2], dut2.first()[1], dut2.first()[0]);
		   dut2.enq(1, unpack('h25));
		endaction
      
		// enqueue some items (to fill mimo)
		action
		   $display("%b %b %b %b %d %x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x", dut2.enqReady(), dut2.deqReady(), dut2.enqReadyN(11), dut2.deqReadyN(0), dut2.count(), 
		      dut2.first()[15], dut2.first()[14], dut2.first()[13], dut2.first()[12], 
		      dut2.first()[11], dut2.first()[10], dut2.first()[9], dut2.first()[8], 
		      dut2.first()[7], dut2.first()[6], dut2.first()[5], dut2.first()[4], 
		      dut2.first()[3], dut2.first()[2], dut2.first()[1], dut2.first()[0]);
		   dut2.enq(11, unpack('h302F2E2D2C2B2A29282726));
		endaction
      
		// full mimo (try removing one)
		action
		   $display("%b %b %b %b %d %x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x", dut2.enqReady(), dut2.deqReady(), dut2.enqReadyN(0), dut2.deqReadyN(1), dut2.count(), 
		      dut2.first()[15], dut2.first()[14], dut2.first()[13], dut2.first()[12], 
		      dut2.first()[11], dut2.first()[10], dut2.first()[9], dut2.first()[8], 
		      dut2.first()[7], dut2.first()[6], dut2.first()[5], dut2.first()[4], 
		      dut2.first()[3], dut2.first()[2], dut2.first()[1], dut2.first()[0]);
		   dut2.deq(1);
		endaction
      
		// simultaneous enq/deq
		action
		   $display("%b %b %b %b %d %x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x", dut2.enqReady(), dut2.deqReady(), dut2.enqReadyN(2), dut2.deqReadyN(1), dut2.count(), 
		      dut2.first()[15], dut2.first()[14], dut2.first()[13], dut2.first()[12], 
		      dut2.first()[11], dut2.first()[10], dut2.first()[9], dut2.first()[8], 
		      dut2.first()[7], dut2.first()[6], dut2.first()[5], dut2.first()[4], 
		      dut2.first()[3], dut2.first()[2], dut2.first()[1], dut2.first()[0]);
		   dut2.enq(2, unpack('h3231));
		   dut2.deq(1);
		endaction
      
		// check full status
		action
		   $display("F: %b %b %b %b %d %x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x", dut2.enqReady(), dut2.deqReady(), dut2.enqReadyN(1), dut2.deqReadyN(1), dut2.count(), 
		      dut2.first()[15], dut2.first()[14], dut2.first()[13], dut2.first()[12], 
		      dut2.first()[11], dut2.first()[10], dut2.first()[9], dut2.first()[8], 
		      dut2.first()[7], dut2.first()[6], dut2.first()[5], dut2.first()[4], 
		      dut2.first()[3], dut2.first()[2], dut2.first()[1], dut2.first()[0]);
		endaction
      
		// dequeue max amount until empty
		action
		   $display("%b %b %b %b %d %x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x", dut2.enqReady(), dut2.deqReady(), dut2.enqReadyN(0), dut2.deqReadyN(16), dut2.count(), 
		      dut2.first()[15], dut2.first()[14], dut2.first()[13], dut2.first()[12], 
		      dut2.first()[11], dut2.first()[10], dut2.first()[9], dut2.first()[8], 
		      dut2.first()[7], dut2.first()[6], dut2.first()[5], dut2.first()[4], 
		      dut2.first()[3], dut2.first()[2], dut2.first()[1], dut2.first()[0]);
		   dut2.deq(16);
		endaction
      
		// dequeue max amount until empty
		action
		   $display("%b %b %b %b %d %x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x", dut2.enqReady(), dut2.deqReady(), dut2.enqReadyN(0), dut2.deqReadyN(16), dut2.count(), 
		      dut2.first()[15], dut2.first()[14], dut2.first()[13], dut2.first()[12], 
		      dut2.first()[11], dut2.first()[10], dut2.first()[9], dut2.first()[8], 
		      dut2.first()[7], dut2.first()[6], dut2.first()[5], dut2.first()[4], 
		      dut2.first()[3], dut2.first()[2], dut2.first()[1], dut2.first()[0]);
		   dut2.deq(16);
		endaction
      
		// dequeue max amount until empty
		action
		   $display("%b %b %b %b %d %x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x,%x", dut2.enqReady(), dut2.deqReady(), dut2.enqReadyN(0), dut2.deqReadyN(16), dut2.count(), 
		      dut2.first()[15], dut2.first()[14], dut2.first()[13], dut2.first()[12], 
		      dut2.first()[11], dut2.first()[10], dut2.first()[9], dut2.first()[8], 
		      dut2.first()[7], dut2.first()[6], dut2.first()[5], dut2.first()[4], 
		      dut2.first()[3], dut2.first()[2], dut2.first()[1], dut2.first()[0]);
		   dut2.deq(16);
		endaction
      
		// verify empty status
		action
		   $display("E: %b %b %b %b %d ", dut2.enqReady(), dut2.deqReady(), dut2.enqReadyN(1), dut2.deqReadyN(16), dut2.count());
		endaction
      
		// action clear/enqueue in same cycle
		action
		   dut2.enq(13, unpack('h3F3E3D3C3B3A39383736353433));
		   dut2.clear();
		endaction

		// verify empty status
		action
		   $display("E: %b %b %b %b %d ", dut2.enqReady(), dut2.deqReady(), dut2.enqReadyN(1), dut2.deqReadyN(16), dut2.count());
		endaction
      
		// action clear/dequeue in same cycle
		dut2.enq(14, unpack('h4D4C4B4A49484746454443424140));
		action
		   dut2.deq(14);
		   dut2.clear();
		endaction

		// verify empty status
		action
		   $display("E: %b %b %b %b %d ", dut2.enqReady(), dut2.deqReady(), dut2.enqReadyN(1), dut2.deqReadyN(16), dut2.count());
		endaction

		// action clear/enqueue/dequeue in same cycle
		dut2.enq(15, unpack('h5C5B5A595857565554535251504F4E));
		action
		   dut2.deq(15);
		   dut2.enq(16, unpack('h6C6B6A696867666564636261605F5E5D));
		   dut2.clear();
		endaction

		// verify empty status
		action
		   $display("E: %b %b %b %b %d ", dut2.enqReady(), dut2.deqReady(), dut2.enqReadyN(1), dut2.deqReadyN(16), dut2.count());
		endaction
      
      
	     endseq);
   
endmodule
