import BRAM::*;
import DefaultValue ::* ;
import GetPut::*;
import ClientServer::*;
import StmtFSM::*;
import Clocks::*;

function BRAMRequest#(Bit#(8), Bit#(8)) makeRequest(Bool write, Bit#(8) addr, Bit#(8) data);
   return BRAMRequest{
                      write: write,
                      responseOnWrite:False,
		      address: addr,
		      datain: data
		      };
endfunction

(* synthesize *)
module sysBRAMTest();
   BRAM_Configure cfg = defaultValue;
   cfg.allowWriteResponseBypass = False;
   BRAM#(Bit#(8), Bit#(8)) dut0 <- mkBRAM2Server(cfg);
   cfg.loadFormat = tagged Hex "bram2.txt";
   BRAM#(Bit#(8), Bit#(8)) dut1 <- mkBRAM2Server(cfg);
   
   Stmt test =
   (seq
       delay(10);
       dut0.portA.request.put(BRAMRequest{ write: True, responseOnWrite : False, address: 8'h00, datain: 8'hFF });
       dut0.portB.request.put(BRAMRequest{ write: True, responseOnWrite : False, address: 8'h01, datain: 8'hFE });
       action
	  dut0.portA.request.put(BRAMRequest{ write: True, responseOnWrite : False, address: 8'h02, datain: 8'hFD });
	  dut0.portB.request.put(BRAMRequest{ write: True, responseOnWrite : False, address: 8'h03, datain: 8'hFC });
       endaction
       action
	  dut0.portA.request.put(BRAMRequest{ write: False, responseOnWrite : False, address: 8'h00, datain: ? });
	  dut0.portB.request.put(BRAMRequest{ write: True, responseOnWrite : False,  address: 8'h04, datain: 8'hFB });
       endaction
       action
	  $display("reading[0x00] = %x", dut0.portA.response.get);
	  dut0.portA.request.put(BRAMRequest{ write: False, responseOnWrite : False, address: 8'h01, datain: ? });
	  dut0.portB.request.put(BRAMRequest{ write: False, responseOnWrite : False, address: 8'h02, datain: ? });
       endaction
       action
	  $display("reading[0x01] = %x", dut0.portA.response.get);
	  $display("reading[0x02] = %x", dut0.portB.response.get);
	  dut0.portA.request.put(BRAMRequest{ write: False, responseOnWrite : False, address: 8'h03, datain: ? });
	  dut0.portB.request.put(BRAMRequest{ write: True, responseOnWrite : False, address: 8'h00, datain: 8'hCD });
       endaction
       $display("reading[0x03] = %x", dut0.portA.response.get);
       
       action
	  dut0.portA.request.put(BRAMRequest{ write: False, responseOnWrite : False, address: 8'h00, datain: ? });
	  dut0.portB.request.put(BRAMRequest{ write: False, responseOnWrite : False, address: 8'h01, datain: ? });
       endaction
       
       action
	  $display("dualread[0x00] = %x", dut0.portA.response.get);
	  $display("dualread[0x01] = %x", dut0.portB.response.get);
	  dut0.portA.request.put(BRAMRequest{ write: False, responseOnWrite : False, address: 8'h02, datain: ? });
	  dut0.portB.request.put(BRAMRequest{ write: False, responseOnWrite : False, address: 8'h03, datain: ? });
       endaction
       $display("dualread[0x02] = %x", dut0.portA.response.get);
       $display("dualread[0x03] = %x", dut0.portB.response.get);
       
       dut0.portA.request.put(BRAMRequest{ write: True, responseOnWrite : False, address: 8'hFF, datain: 8'h54 });
       dut0.portA.request.put(BRAMRequest{ write: False, responseOnWrite : False,  address: 8'hFF, datain: ? });
       delay(20);
       $display("dualread[0xFF] = %x", dut0.portA.response.get);
    
       delay(10);
       dut0.portA.request.put(makeRequest(True, 0, 8'hFF));
       dut0.portA.request.put(makeRequest(True, 1, 8'hFE));
       dut0.portA.request.put(makeRequest(True, 2, 8'hFD));
       dut0.portA.request.put(makeRequest(True, 3, 8'hFC));
       dut0.portA.request.put(makeRequest(True, 4, 8'hFB));
       delay(10);
//        par
// 	  seq
// 	     dut0.portA.request.put(makeRequest(False, 0, ?));
// 	     dut0.portA.request.put(makeRequest(False, 1, ?));
// 	     dut0.portA.request.put(makeRequest(False, 2, ?));
// 	     dut0.portA.request.put(makeRequest(False, 3, ?));
// 	     dut0.portA.request.put(makeRequest(False, 4, ?));
// 	     delay(10);
// 	  endseq
// 	  seq
// 	     delay(10);
// 	     $display("%x", dut0.portA.response.get);
// 	     delay(10);
// 	     $display("%x", dut0.portA.response.get);
// 	     delay(10);
// 	     $display("%x", dut0.portA.response.get);
// 	     delay(10);
// 	     $display("%x", dut0.portA.response.get);
// 	     delay(10);
// 	     $display("%x", dut0.portA.response.get);
// 	     delay(10);
// 	  endseq
//        endpar
//        delay(100);
//        par
// 	  seq
// 	     dut0.portA.request.put(makeRequest(False, 0, ?));
// 	     dut0.portA.request.put(makeRequest(False, 1, ?));
// 	     dut0.portA.request.put(makeRequest(False, 2, ?));
// 	     dut0.portA.request.put(makeRequest(False, 3, ?));
// 	     dut0.portA.request.put(makeRequest(False, 4, ?));
// 	     delay(10);
// 	  endseq
// 	  seq
// 	     $display("%t %x", $time, dut0.portA.response.get);
// 	     $display("%t %x", $time, dut0.portA.response.get);
// 	     $display("%t %x", $time, dut0.portA.response.get);
// 	     $display("%t %x", $time, dut0.portA.response.get);
// 	     $display("%t %x", $time, dut0.portA.response.get);
// 	  endseq
//        endpar
       delay(100);
       action 
	  dut1.portA.request.put(makeRequest(False, 8'h00, ?));
	  dut1.portB.request.put(makeRequest(False, 8'h01, ?));
       endaction
       action 
	  $display("dut1read[0] = %x", dut1.portA.response.get);
	  $display("dut1read[1] = %x", dut1.portB.response.get);
	  dut1.portA.request.put(makeRequest(False, 8'h02, ?));
	  dut1.portB.request.put(makeRequest(False, 8'h03, ?));
       endaction
       action 
	  $display("dut1read[2] = %x", dut1.portA.response.get);
	  $display("dut1read[3] = %x", dut1.portB.response.get);
	  dut1.portA.request.put(makeRequest(False, 8'h04, ?));
	  dut1.portB.request.put(makeRequest(False, 8'h05, ?));
       endaction
       action 
	  $display("dut1read[4] = %x", dut1.portA.response.get);
	  $display("dut1read[5] = %x", dut1.portB.response.get);
	  dut1.portA.request.put(makeRequest(True, 8'h04, 8'hEE));
	  dut1.portB.request.put(makeRequest(True, 8'h05, 8'hDD));
       endaction
       dut1.portA.request.put(makeRequest(False, 8'h04, ?));
       dut1.portB.request.put(makeRequest(False, 8'h05, ?));
       action 
	  $display("dut1read[4] = %x", dut1.portA.response.get);
	  $display("dut1read[5] = %x", dut1.portB.response.get);
       endaction	 
       delay(10);
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
       delay(100);
       $finish;
    endseq);
   
   let in_reset <- isResetAssertedDirect;
   
   
   let fsm <- mkFSMWithPred(test, !in_reset);
   
   rule do_start;
      fsm.start;
   endrule
   
endmodule
