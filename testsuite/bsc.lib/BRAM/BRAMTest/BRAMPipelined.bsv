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

function BRAMRequestBE#(a, d, n) makeRequestBE(Bit#(n) write, a addr, d data);
   return BRAMRequestBE{
			writeen: write,
			address: addr,
			datain: data
			};
endfunction

(* synthesize *)
module sysBRAMPipelined();
   BRAM#(Bit#(8), Bit#(8)) dut0 <- mkBRAM(False);
   BRAM#(Bit#(8), Bit#(8)) dut01 <- mkBRAM(True);
   BRAM#(Bit#(8), Bit#(8)) dut1 <- mkBRAMLoad(True, "bram2.txt");

   BRAM1Port#(Bit#(8), Bit#(8)) dut2 <- mkBRAM1(True);
   BRAM1Port#(Bit#(8), Bit#(8)) dut3 <- mkBRAM1Load(True, "bram2.txt");
   
   BRAM1PortBE#(Bit#(8), Bit#(32), 4) dut4 <- mkBRAM1BE(True);
   BRAM1PortBE#(Bit#(8), Bit#(32), 4) dut5 <- mkBRAM1BELoad(True, "bram2.txt");
   
   Stmt test =
   (seq
       delay(10);
       $display("Non-Pipelined write->read");
       action
	  dut0.portA.request.put(makeRequest(True, 0, 8'hFF));
	  $display("[%t] BRAM[0] <= FF", $time);
       endaction
       action
	  dut0.portA.request.put(makeRequest(False, 0, ?));
	  $display("[%t] read request", $time);
       endaction
       $display("[%t] BRAM[0] => %x", $time, dut0.portA.response.get);

       $display("Pipelined write->read");
       action
	  dut01.portA.request.put(makeRequest(True, 0, 8'hFE));
	  $display("[%t] BRAM[0] <= FE", $time);
       endaction
       action
	  dut01.portA.request.put(makeRequest(False, 0, ?));
	  $display("[%t] read request", $time);
       endaction
       $display("[%t] BRAM[0] => %x", $time, dut01.portA.response.get);
       
       $display("dut1");
    // dut1
       action
	  dut1.portA.request.put(makeRequest(False, 0, ?));
	  $display("[%t] read request", $time);
       endaction
       $display("[%t] BRAM[0] => %x", $time, dut1.portA.response.get);

       $display("Non-Pipelined write->read");
       action
	  dut0.portB.request.put(makeRequest(True, 0, 8'hFF));
	  $display("[%t] BRAM[0] <= FF", $time);
       endaction
       action
	  dut0.portB.request.put(makeRequest(False, 0, ?));
	  $display("[%t] read request", $time);
       endaction
       $display("[%t] BRAM[0] => %x", $time, dut0.portB.response.get);

       $display("Pipelined write->read");
       action
	  dut01.portB.request.put(makeRequest(True, 0, 8'hFE));
	  $display("[%t] BRAM[0] <= FE", $time);
       endaction
       action
	  dut01.portB.request.put(makeRequest(False, 0, ?));
	  $display("[%t] read request", $time);
       endaction
       $display("[%t] BRAM[0] => %x", $time, dut01.portB.response.get);
       
       $display("dut1");
    // dut1
       action
	  dut1.portB.request.put(makeRequest(False, 0, ?));
	  $display("[%t] read request", $time);
       endaction
       $display("[%t] BRAM[0] => %x", $time, dut1.portB.response.get);

       $display("dut2");
    // dut2
       action
	  dut2.portA.request.put(makeRequest(True, 0, 8'hFD));
	  $display("[%t] BRAM[0] <= FD", $time);
       endaction
       action
	  dut2.portA.request.put(makeRequest(False, 0, ?));
	  $display("[%t] read request", $time);
       endaction
       $display("[%t] BRAM[0] => %x", $time, dut2.portA.response.get);

       $display("dut3");
    // dut3
       action
	  dut3.portA.request.put(makeRequest(False, 3, ?));
	  $display("[%t] read request", $time);
       endaction
       $display("[%t] BRAM[3] => %x", $time, dut3.portA.response.get);

       $display("dut4");
    // dut4
       action
	  dut4.portA.request.put(makeRequestBE(14, 0, -1));
	  $display("[%t] BRAM[0] <= FFFFFFFF (%8b)", $time, 8'd14);
       endaction
       action
	  dut4.portA.request.put(makeRequestBE(0, 0, ?));
	  $display("[%t] read request", $time);
       endaction
       $display("[%t] BRAM[0] => %x", $time, dut4.portA.response.get);

       $display("dut5");
    // dut5
       action
	  dut5.portA.request.put(makeRequestBE(0, 5, ?));
	  $display("[%t] read request", $time);
       endaction
       $display("[%t] BRAM[5] => %x", $time, dut5.portA.response.get);
    
       delay(10);
    
    endseq);
   
   mkAutoFSM(test);
   
endmodule
