import BRAM::*;
import GetPut::*;
import ClientServer::*;
import StmtFSM::*;
import Clocks::*;

function BRAMRequest#(Bit#(8), Bit#(8)) makeRequest(Bool write, Bit#(8) addr, Bit#(8) data);
   return BRAMRequest{
		      write: write,
		      address: addr,
		      datain: data
		      };
endfunction

(* synthesize *)
module sysBRAMLoadTest();
   let        clkdiv1 <- mkClockDivider(7);
   let        clkdiv2 <- mkClockDivider(5);

   Clock      clk     <- exposeCurrentClock;
   Clock      clk1     = clkdiv1.slowClock;
   Clock      clk2     = clkdiv2.slowClock;
   
   Reset      rst     <- exposeCurrentReset;
   Reset      rst1    <- mkAsyncReset(3, rst, clk1);
   Reset      rst2    <- mkAsyncReset(3, rst, clk2);
  
   BRAM#(Bit#(8), Bit#(8)) dut0 <- mkSyncBRAM(False, clk1, rst1, clk2, rst2);
   BRAM#(Bit#(8), Bit#(8)) dut1 <- mkSyncBRAMLoad(False, clk1, rst1, clk2, rst2, "bram.txt");

   Stmt testA =
   (seq
       delay(10);
       dut0.portA.request.put(BRAMRequest{ write: True, address: 8'h00, datain: 8'hFF });
       dut0.portA.request.put(BRAMRequest{ write: True, address: 8'h02, datain: 8'hFD });
       dut0.portA.request.put(BRAMRequest{ write: False, address: 8'h00, datain: ? });
       action
	  $display("reading[0x00] = %x", dut0.portA.response.get);
	  dut0.portA.request.put(BRAMRequest{ write: False, address: 8'h01, datain: ? });
       endaction
       action
	  $display("reading[0x01] = %x", dut0.portA.response.get);
	  dut0.portA.request.put(BRAMRequest{ write: False, address: 8'h03, datain: ? });
       endaction
       $display("reading[0x03] = %x", dut0.portA.response.get);
       
       dut0.portA.request.put(BRAMRequest{ write: False, address: 8'h00, datain: ? });
       
       action
	  $display("dualread[0x00] = %x", dut0.portA.response.get);
	  dut0.portA.request.put(BRAMRequest{ write: False, address: 8'h02, datain: ? });
       endaction
       $display("dualread[0x02] = %x", dut0.portA.response.get);
       
       dut0.portA.request.put(BRAMRequest{ write: True, address: 8'hFF, datain: 8'h54 });
       dut0.portA.request.put(BRAMRequest{ write: False, address: 8'hFF, datain: ? });
       delay(20);
       $display("dualread[0xFF] = %x", dut0.portA.response.get);
       delay(100);       

       dut1.portA.request.put(makeRequest(False, 8'h00, ?));
       action 
	  $display("dut1read[0] = %x", dut1.portA.response.get);
	  dut1.portA.request.put(makeRequest(False, 8'h02, ?));
       endaction
       action 
	  $display("dut1read[2] = %x", dut1.portA.response.get);
	  dut1.portA.request.put(makeRequest(False, 8'h04, ?));
       endaction
       action 
	  $display("dut1read[4] = %x", dut1.portA.response.get);
	  dut1.portA.request.put(makeRequest(True, 8'h04, 8'hEE));
       endaction
       dut1.portA.request.put(makeRequest(False, 8'h04, ?));
       $display("dut1read[4] = %x", dut1.portA.response.get);
       delay(100);
    
       delay(300);
       dut1.portA.request.put(makeRequest(True, 0, 8'hFF));
       dut1.portA.request.put(makeRequest(True, 1, 8'hFE));
       dut1.portA.request.put(makeRequest(True, 2, 8'hFD));
       dut1.portA.request.put(makeRequest(True, 3, 8'hFC));
       dut1.portA.request.put(makeRequest(True, 4, 8'hFB));
       delay(10);
//        par
// 	  seq
// 	     dut1.portA.request.put(makeRequest(False, 0, ?));
// 	     dut1.portA.request.put(makeRequest(False, 1, ?));
// 	     dut1.portA.request.put(makeRequest(False, 2, ?));
// 	     dut1.portA.request.put(makeRequest(False, 3, ?));
// 	     dut1.portA.request.put(makeRequest(False, 4, ?));
// 	     delay(10);
// 	  endseq
// 	  seq
// 	     delay(10);
// 	     $display("%x", dut1.portA.response.get);
// 	     delay(10);
// 	     $display("%x", dut1.portA.response.get);
// 	     delay(10);
// 	     $display("%x", dut1.portA.response.get);
// 	     delay(10);
// 	     $display("%x", dut1.portA.response.get);
// 	     delay(10);
// 	     $display("%x", dut1.portA.response.get);
// 	     delay(10);
// 	  endseq
//        endpar
//        delay(100);
//        par
// 	  seq
// 	     dut1.portA.request.put(makeRequest(False, 0, ?));
// 	     dut1.portA.request.put(makeRequest(False, 1, ?));
// 	     dut1.portA.request.put(makeRequest(False, 2, ?));
// 	     dut1.portA.request.put(makeRequest(False, 3, ?));
// 	     dut1.portA.request.put(makeRequest(False, 4, ?));
// 	     delay(10);
// 	  endseq
// 	  seq
// 	     $display("%t %x", $time, dut1.portA.response.get);
// 	     $display("%t %x", $time, dut1.portA.response.get);
// 	     $display("%t %x", $time, dut1.portA.response.get);
// 	     $display("%t %x", $time, dut1.portA.response.get);
// 	     $display("%t %x", $time, dut1.portA.response.get);
// 	  endseq
//        endpar
       delay(500);

    endseq);
   
   mkAutoFSM(testA, clocked_by clk1, reset_by rst1);
   
   Stmt testB =
   (seq
       delay(10);
       dut0.portB.request.put(BRAMRequest{ write: True, address: 8'h01, datain: 8'hFE });
       dut0.portB.request.put(BRAMRequest{ write: True, address: 8'h03, datain: 8'hFC });
       dut0.portB.request.put(BRAMRequest{ write: True,  address: 8'h04, datain: 8'hFB });
       delay(5);
       dut0.portB.request.put(BRAMRequest{ write: False, address: 8'h02, datain: ? });
       action
	  $display("reading[0x02] = %x", dut0.portB.response.get);
	  dut0.portB.request.put(BRAMRequest{ write: True, address: 8'h00, datain: 8'hCD });
       endaction
       dut0.portB.request.put(BRAMRequest{ write: False, address: 8'h01, datain: ? });
       
       action
	  $display("dualread[0x01] = %x", dut0.portB.response.get);
	  dut0.portB.request.put(BRAMRequest{ write: False, address: 8'h03, datain: ? });
       endaction
       $display("dualread[0x03] = %x", dut0.portB.response.get);
       
       delay(100);       
    
       dut1.portB.request.put(makeRequest(False, 8'h01, ?));
       action
	  $display("dut1read[1] = %x", dut1.portB.response.get);
	  dut1.portB.request.put(makeRequest(False, 8'h03, ?));
       endaction
       action 
	  $display("dut1read[3] = %x", dut1.portB.response.get);
	  dut1.portB.request.put(makeRequest(False, 8'h05, ?));
       endaction
       action 
	  $display("dut1read[5] = %x", dut1.portB.response.get);
	  dut1.portB.request.put(makeRequest(True, 8'h05, 8'hDD));
       endaction
       dut1.portB.request.put(makeRequest(False, 8'h05, ?));
       $display("dut1read[5] = %x", dut1.portB.response.get);

       delay(300);
       dut1.portB.request.put(makeRequest(True, 0, 8'hFF));
       dut1.portB.request.put(makeRequest(True, 1, 8'hFE));
       dut1.portB.request.put(makeRequest(True, 2, 8'hFD));
       dut1.portB.request.put(makeRequest(True, 3, 8'hFC));
       dut1.portB.request.put(makeRequest(True, 4, 8'hFB));
       delay(10);
//        par
// 	  seq
// 	     dut1.portB.request.put(makeRequest(False, 0, ?));
// 	     dut1.portB.request.put(makeRequest(False, 1, ?));
// 	     dut1.portB.request.put(makeRequest(False, 2, ?));
// 	     dut1.portB.request.put(makeRequest(False, 3, ?));
// 	     dut1.portB.request.put(makeRequest(False, 4, ?));
// 	     delay(10);
// 	  endseq
// 	  seq
// 	     delay(10);
// 	     $display("%x", dut1.portB.response.get);
// 	     delay(10);
// 	     $display("%x", dut1.portB.response.get);
// 	     delay(10);
// 	     $display("%x", dut1.portB.response.get);
// 	     delay(10);
// 	     $display("%x", dut1.portB.response.get);
// 	     delay(10);
// 	     $display("%x", dut1.portB.response.get);
// 	     delay(10);
// 	  endseq
//        endpar
//        delay(100);
//        par
// 	  seq
// 	     dut1.portB.request.put(makeRequest(False, 0, ?));
// 	     dut1.portB.request.put(makeRequest(False, 1, ?));
// 	     dut1.portB.request.put(makeRequest(False, 2, ?));
// 	     dut1.portB.request.put(makeRequest(False, 3, ?));
// 	     dut1.portB.request.put(makeRequest(False, 4, ?));
// 	     delay(10);
// 	  endseq
// 	  seq
// 	     $display("%t %x", $time, dut1.portB.response.get);
// 	     $display("%t %x", $time, dut1.portB.response.get);
// 	     $display("%t %x", $time, dut1.portB.response.get);
// 	     $display("%t %x", $time, dut1.portB.response.get);
// 	     $display("%t %x", $time, dut1.portB.response.get);
// 	  endseq
//        endpar
       delay(500);
    endseq);
   
   mkAutoFSM(testB, clocked_by clk2, reset_by rst2);

   
endmodule
