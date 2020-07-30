package Scoreboard;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

import EthFrame::*;
import FIFOF::*;
import Control::*;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

interface Scoreboard;
   interface Control cntrl;
   method Action sent_from_mac_side(Frame frame);
   method Action sent_from_phy_side(Frame frame);
   method Action received_by_mac_side(Frame frame);
   method Action received_by_phy_side(Frame frame);
endinterface


(* synthesize *)
module mkScoreboard (Scoreboard);
   
   Reg#(Bool) initialized <- mkReg(False);
   FIFOF#(Frame) to_mac_side_fifo  <-  mkSizedFIFOF(16); 
   FIFOF#(Frame) to_phy_side_fifo  <-  mkSizedFIFOF(16); 
   
   Reg#(Bit#(16)) receive_test_count <- mkReg(0);
   Reg#(Bit#(16)) transmit_test_count <- mkReg(0);
   Reg#(Bit#(16)) receive_test_fail_count <- mkReg(0);
   Reg#(Bit#(16)) transmit_test_fail_count <- mkReg(0);
   
   rule finish ((receive_test_count + transmit_test_count) > 50);
      $finish;
   endrule
   
   interface Control cntrl;
      method Action init();
	 to_mac_side_fifo.clear();
	 to_phy_side_fifo.clear();
	 initialized <= True;
      endmethod
   endinterface
   
   method Action sent_from_mac_side(Frame frame) if (initialized); 
      transmit_test_count <= transmit_test_count + 1;
      to_phy_side_fifo.enq(frame);
   endmethod
   
   method Action sent_from_phy_side(Frame frame) if (initialized);
      receive_test_count <= receive_test_count + 1;
      to_mac_side_fifo.enq(frame);
   endmethod
   
   method Action received_by_mac_side(Frame frame);
      let expected = to_mac_side_fifo.first();
      to_mac_side_fifo.deq();
      if (expected == frame)
	 action
	    $display("------------------------------------------------\n(%5d)       DUT RECEIVE TEST RESULT            \nFrame Matches expected result!", $time);
	    displayFrame(frame);
	    $display("------------------------------------------------");
	 endaction
      else
	 action
	    receive_test_fail_count <= receive_test_fail_count + 1;
	    $display("------------------------------------------------\n(%5d)       DUT RECEIVE TEST RESULT            \nFrames Don't Match!!!", $time);
	    displayFrame(expected);
	    displayFrame(frame);
	    $display("------------------------------------------------");
	 endaction
   endmethod
   
   method Action received_by_phy_side(Frame frame);
      let expected = to_phy_side_fifo.first();
      to_phy_side_fifo.deq();
      if (expected == frame)
	 action
	    $display("------------------------------------------------\n(%5d)       DUT TRANSMIT TEST RESULT           \nFrame Matches expected result!", $time);
	    displayFrame(frame);
	    $display("------------------------------------------------");
	 endaction
      else
	 action
	    transmit_test_fail_count <= transmit_test_fail_count + 1;
	    $display("------------------------------------------------\n(%5d)       DUT TRANSMIT TEST RESULT           \nFrames Don't Match!!!", $time);
	    displayFrame(expected);
	    displayFrame(frame);
	    $display("------------------------------------------------");
	 endaction
   endmethod
   
endmodule


(* synthesize *)
module mkDummyScoreboard (Scoreboard);
   
   Reg#(Bool) initialized <- mkReg(False);
   Reg#(Bit#(16)) receive_test_count <- mkReg(0);
   Reg#(Bit#(16)) transmit_test_count <- mkReg(0);
   
   rule finish ((receive_test_count + transmit_test_count) > 10);
      $finish;
   endrule
   
   interface Control cntrl;
      method Action init();
	 initialized <= True;
      endmethod
   endinterface
   
   method Action sent_from_mac_side(Frame frame) if (initialized); 
      transmit_test_count <= transmit_test_count + 1;
   endmethod
   
   method Action sent_from_phy_side(Frame frame) if (initialized);
      receive_test_count <= receive_test_count + 1;
   endmethod
   
   method Action received_by_mac_side(Frame frame);

   endmethod
   
   method Action received_by_phy_side(Frame frame);

   endmethod
   
endmodule

endpackage
