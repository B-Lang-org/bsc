import BRAM::*;
import GetPut::*;
import ClientServer::*;
import StmtFSM::*;
import Clocks::*;

function BRAMRequest#(a, b) makeRequest(Bool write, a addr, b data);
   return BRAMRequest{
                      write: write,
                      responseOnWrite:False,
		      address: addr,
		      datain: data
		      };
endfunction

function BRAMRequestBE#(a, b, n) makeRequestBE(Bit#(n) write, a addr, b data);
   return BRAMRequestBE{
			writeen: write,
                        responseOnWrite:False,
			address: addr,
			datain: data
			};
endfunction

// Test that DefaultValue or Eq instances are NOT required.
typedef struct {
   Bit#(8)  b8;
   } B8
deriving(Bits);


(* synthesize *)
module sysBRAMWidthTest();

   // Test BRAM of various widths

   // XXX for now, just show that wide BE is not (yet) supported
   BRAM1PortBE#(Bit#(8), Bit#(520), 65) dut0 <- mkBRAM1ServerBE(defaultValue);
   
   Stmt test =
   seq
      delay(10);
      dut0.portA.request.put(makeRequestBE(2, 8'hFF, 0));
      dut0.portA.request.put(makeRequestBE(1, 8'hFE, 0));
      dut0.portA.request.put(makeRequestBE(0, 8'hFF, ?));
      action
	 let data <- dut0.portA.response.get;
	 $display("%h", data);
      endaction

   endseq;
   
   mkAutoFSM(test);

endmodule
