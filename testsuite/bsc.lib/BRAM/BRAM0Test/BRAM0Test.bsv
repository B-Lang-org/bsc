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
module sysBRAM0Test();
   BRAM#(Bit#(0), B8)      dut0 <- mkBRAM2Server(defaultValue);
   BRAM#(Bit#(8), Bit#(0)) dut1 <- mkBRAM2Server(defaultValue);
   BRAM#(Bit#(0), Bit#(0)) dut2 <- mkBRAM2Server(defaultValue);

   let cfg1 = defaultValue ;
   cfg1.loadFormat = tagged Hex "bram2.txt" ;
   BRAM#(Bit#(0), Bit#(8)) dut3 <- mkBRAM2Server(cfg1);
   BRAM#(Bit#(8), Bit#(0)) dut4 <- mkBRAM2Server(cfg1);
   BRAM#(Bit#(0), Bit#(0)) dut5 <- mkBRAM2Server(cfg1);

   BRAM1Port#(Bit#(0), Bit#(8)) dut6 <- mkBRAM1Server(defaultValue);
   BRAM1Port#(Bit#(8), Bit#(0)) dut7 <- mkBRAM1Server(defaultValue);
   BRAM1Port#(Bit#(0), Bit#(0)) dut8 <- mkBRAM1Server(defaultValue);
   
   BRAM1Port#(Bit#(0), Bit#(8)) dut9 <- mkBRAM1Server(cfg1);
   BRAM1Port#(Bit#(8), Bit#(0)) dut10 <- mkBRAM1Server(cfg1);
   BRAM1Port#(Bit#(0), Bit#(0)) dut11 <- mkBRAM1Server(cfg1);

   BRAM1PortBE#(Bit#(0), Bit#(8), 1) dut12 <- mkBRAM1ServerBE(defaultValue);
   BRAM1PortBE#(Bit#(8), Bit#(0), 2) dut13 <- mkBRAM1ServerBE(defaultValue);
   BRAM1PortBE#(Bit#(0), Bit#(0), 3) dut14 <- mkBRAM1ServerBE(defaultValue);

   BRAM1PortBE#(Bit#(0), Bit#(8), 1) dut15 <- mkBRAM1ServerBE(cfg1);
   BRAM1PortBE#(Bit#(8), Bit#(0), 2) dut16 <- mkBRAM1ServerBE(cfg1);
   BRAM1PortBE#(Bit#(0), Bit#(0), 3) dut17 <- mkBRAM1ServerBE(cfg1);

   let cfg2 = defaultValue ;
   cfg2.latency=2;
   BRAM#(Bit#(0), Bit#(8)) dut20 <- mkBRAM2Server(cfg2);
   BRAM#(Bit#(8), Bit#(0)) dut21 <- mkBRAM2Server(cfg2);
   BRAM#(Bit#(0), Bit#(0)) dut22 <- mkBRAM2Server(cfg2);

   let cfg3 = cfg2;
   cfg3.loadFormat = tagged Hex "bram2.txt" ;
   BRAM#(Bit#(0), Bit#(8)) dut23 <- mkBRAM2Server(cfg3);
   BRAM#(Bit#(8), Bit#(0)) dut24 <- mkBRAM2Server(cfg3);
   BRAM#(Bit#(0), Bit#(0)) dut25 <- mkBRAM2Server(cfg3);

   BRAM1Port#(Bit#(0), Bit#(8)) dut26 <- mkBRAM1Server(cfg2);
   BRAM1Port#(Bit#(8), Bit#(0)) dut27 <- mkBRAM1Server(cfg2);
   BRAM1Port#(Bit#(0), Bit#(0)) dut28 <- mkBRAM1Server(cfg2);

   BRAM1Port#(Bit#(0), Bit#(8)) dut29 <- mkBRAM1Server(cfg3);
   BRAM1Port#(Bit#(8), Bit#(0)) dut30 <- mkBRAM1Server(cfg3);
   BRAM1Port#(Bit#(0), Bit#(0)) dut31 <- mkBRAM1Server(cfg3);
   
   BRAM1PortBE#(Bit#(0), Bit#(8), 1) dut32 <- mkBRAM1ServerBE(cfg2);
   BRAM1PortBE#(Bit#(8), Bit#(0), 2) dut33 <- mkBRAM1ServerBE(cfg2);
   BRAM1PortBE#(Bit#(0), Bit#(0), 3) dut34 <- mkBRAM1ServerBE(cfg2);

   BRAM1PortBE#(Bit#(0), Bit#(8), 1) dut35 <- mkBRAM1ServerBE(cfg3);
   BRAM1PortBE#(Bit#(8), Bit#(0), 2) dut36 <- mkBRAM1ServerBE(cfg3);
   BRAM1PortBE#(Bit#(0), Bit#(0), 3) dut37 <- mkBRAM1ServerBE(cfg3);
   
   Stmt test =
   seq
      delay(10);
      dut0.portA.request.put(makeRequest(True, 0, unpack(8'hFF)));
      dut0.portB.request.put(makeRequest(True, 0, unpack(8'hFE)));
      dut0.portA.request.put(makeRequest(False, 0, ?));
      action
	 let data <- dut0.portA.response.get;
	 $display("%x", data);
      endaction

      delay(10);
      dut1.portA.request.put(makeRequest(True, 8'hFF, 0));
      dut1.portB.request.put(makeRequest(True, 8'hFE, 0));
      dut1.portA.request.put(makeRequest(False, 8'hFF, ?));
      action
	 let data <- dut1.portA.response.get;
	 $display("%x", data);
      endaction

      delay(10);
      dut2.portA.request.put(makeRequest(True, 0, 0));
      dut2.portA.request.put(makeRequest(False, 0, ?));
      action
	 let data <- dut2.portA.response.get;
	 $display("%x", data);
      endaction

      delay(10);
      dut3.portA.request.put(makeRequest(True, 0, 8'hFF));
      dut3.portB.request.put(makeRequest(True, 0, 8'hFE));
      dut3.portA.request.put(makeRequest(False, 0, ?));
      action
	 let data <- dut3.portA.response.get;
	 $display("%x", data);
      endaction

      delay(10);
      dut4.portA.request.put(makeRequest(True, 8'hFF, 0));
      dut4.portB.request.put(makeRequest(True, 8'hFE, 0));
      dut4.portA.request.put(makeRequest(False, 8'hFF, ?));
      action
	 let data <- dut4.portA.response.get;
	 $display("%x", data);
      endaction

      delay(10);
      dut5.portA.request.put(makeRequest(True, 0, 0));
      dut5.portA.request.put(makeRequest(False, 0, ?));
      action
	 let data <- dut5.portA.response.get;
	 $display("%x", data);
      endaction
      
      delay(10); // addr = Bit#(0)
      dut6.portA.request.put(makeRequest(True, 0, 8'hFF));
      dut6.portA.request.put(makeRequest(True, 0, 8'hFE));
      dut6.portA.request.put(makeRequest(False, 0, ?));
      action
	 let data <- dut6.portA.response.get;
	 $display("%x dut6", data);
      endaction

      delay(10);
      dut7.portA.request.put(makeRequest(True, 8'hFF, 0));
      dut7.portA.request.put(makeRequest(True, 8'hFE, 0));
      dut7.portA.request.put(makeRequest(False, 8'hFF, ?));
      action
	 let data <- dut7.portA.response.get;
	 $display("%x", data);
      endaction

      delay(10);
      dut8.portA.request.put(makeRequest(True, 0, 0));
      dut8.portA.request.put(makeRequest(False, 0, ?));
      action
	 let data <- dut8.portA.response.get;
	 $display("%x", data);
      endaction
      
      delay(10);
      dut9.portA.request.put(makeRequest(True, 0, 8'hFF));
      dut9.portA.request.put(makeRequest(True, 0, 8'hFE));
      dut9.portA.request.put(makeRequest(False, 0, ?));
      action
	 let data <- dut9.portA.response.get;
	 $display("%x dut 9", data);
      endaction

      delay(10);
      dut10.portA.request.put(makeRequest(True, 8'hFF, 0));
      dut10.portA.request.put(makeRequest(True, 8'hFE, 0));
      dut10.portA.request.put(makeRequest(False, 8'hFF, ?));
      action
	 let data <- dut10.portA.response.get;
	 $display("%x", data);
      endaction

      delay(10);
      dut11.portA.request.put(makeRequest(True, 0, 0));
      dut11.portA.request.put(makeRequest(False, 0, ?));
      action
	 let data <- dut11.portA.response.get;
	 $display("%x", data);
      endaction
      
      delay(10);
      dut12.portA.request.put(makeRequestBE(1, 0, 8'hFF));
      dut12.portA.request.put(makeRequestBE(1, 0, 8'hFE));
      dut12.portA.request.put(makeRequestBE(0, 0, ?));
      action
	 let data <- dut12.portA.response.get;
	 $display("%x dut 12", data);
      endaction

      delay(10);
      dut13.portA.request.put(makeRequestBE(2, 8'hFF, 0));
      dut13.portA.request.put(makeRequestBE(1, 8'hFE, 0));
      dut13.portA.request.put(makeRequestBE(0, 8'hFF, ?));
      action
	 let data <- dut13.portA.response.get;
	 $display("%x", data);
      endaction

      delay(10);
      dut14.portA.request.put(makeRequestBE(5, 0, 0));
      dut14.portA.request.put(makeRequestBE(0, 0, ?));
      action
	 let data <- dut14.portA.response.get;
	 $display("%x", data);
      endaction
      
      delay(10); // dut15 has addr width of 0
      dut15.portA.request.put(makeRequestBE(1, 0, 8'hFF));
      dut15.portA.request.put(makeRequestBE(1, 0, 8'hFE));
      dut15.portA.request.put(makeRequestBE(0, 0, ?));
      action
	 let data <- dut15.portA.response.get;
	 $display("%x dut 15", data);
      endaction

      delay(10);
      dut16.portA.request.put(makeRequestBE(2, 8'hFF, 0));
      dut16.portA.request.put(makeRequestBE(1, 8'hFE, 0));
      dut16.portA.request.put(makeRequestBE(0, 8'hFF, ?));
      action
	 let data <- dut16.portA.response.get;
	 $display("%x", data);
      endaction

      delay(10); // addr width is 0
      dut17.portA.request.put(makeRequestBE(0, 0, 0));
      dut17.portA.request.put(makeRequestBE(0, 0, ?));
      action
	 let data <- dut17.portA.response.get;
	 $display("%x dut 17", data);
      endaction

      delay(10);
      dut20.portA.request.put(makeRequest(True, 0, 8'hFF));
      dut20.portB.request.put(makeRequest(True, 0, 8'hFE));
      dut20.portA.request.put(makeRequest(False, 0, ?));
      action
	 let data <- dut20.portA.response.get;
	 $display("%x", data);
      endaction

      delay(10);
      dut21.portA.request.put(makeRequest(True, 8'hFF, 0));
      dut21.portB.request.put(makeRequest(True, 8'hFE, 0));
      dut21.portA.request.put(makeRequest(False, 8'hFF, ?));
      action
	 let data <- dut21.portA.response.get;
	 $display("%x", data);
      endaction

      delay(10);
      dut22.portA.request.put(makeRequest(True, 0, 0));
      dut22.portA.request.put(makeRequest(False, 0, ?));
      action
	 let data <- dut22.portA.response.get;
	 $display("%x", data);
      endaction

      delay(10);
      dut23.portA.request.put(makeRequest(True, 0, 8'hFF));
      dut23.portB.request.put(makeRequest(True, 0, 8'hFE));
      dut23.portA.request.put(makeRequest(False, 0, ?));
      action
	 let data <- dut23.portA.response.get;
	 $display("%x", data);
      endaction

      delay(10);
      dut24.portA.request.put(makeRequest(True, 8'hFF, 0));
      dut24.portB.request.put(makeRequest(True, 8'hFE, 0));
      dut24.portA.request.put(makeRequest(False, 8'hFF, ?));
      action
	 let data <- dut24.portA.response.get;
	 $display("%x", data);
      endaction

      delay(10);
      dut25.portA.request.put(makeRequest(True, 0, 0));
      dut25.portA.request.put(makeRequest(False, 0, ?));
      action
	 let data <- dut25.portA.response.get;
	 $display("%x", data);
      endaction
      
      delay(10); // address size 0
      dut26.portA.request.put(makeRequest(True, 0, 8'hFF));
      dut26.portA.request.put(makeRequest(True, 0, 8'hFE));
      dut26.portA.request.put(makeRequest(False, 0, ?));
      action
	 let data <- dut26.portA.response.get;
	 $display("%x dut 26", data);
      endaction

      delay(10);
      dut27.portA.request.put(makeRequest(True, 8'hFF, 0));
      dut27.portA.request.put(makeRequest(True, 8'hFE, 0));
      dut27.portA.request.put(makeRequest(False, 8'hFF, ?));
      action
	 let data <- dut27.portA.response.get;
	 $display("%x", data);
      endaction

      delay(10);
      dut28.portA.request.put(makeRequest(True, 0, 0));
      dut28.portA.request.put(makeRequest(False, 0, ?));
      action
	 let data <- dut28.portA.response.get;
	 $display("%x", data);
      endaction
      
      delay(10);
      dut29.portA.request.put(makeRequest(True, 0, 8'hFF));
      dut29.portA.request.put(makeRequest(True, 0, 8'hFE));
      dut29.portA.request.put(makeRequest(False, 0, ?));
      action
	 let data <- dut29.portA.response.get;
	 $display("%x dut29", data);
      endaction

      delay(10);
      dut30.portA.request.put(makeRequest(True, 8'hFF, 0));
      dut30.portA.request.put(makeRequest(True, 8'hFE, 0));
      dut30.portA.request.put(makeRequest(False, 8'hFF, ?));
      action
	 let data <- dut30.portA.response.get;
	 $display("%x", data);
      endaction

      delay(10);
      dut31.portA.request.put(makeRequest(True, 0, 0));
      dut31.portA.request.put(makeRequest(False, 0, ?));
      action
	 let data <- dut31.portA.response.get;
	 $display("%x", data);
      endaction
      
      delay(10); // address size 0
      dut32.portA.request.put(makeRequestBE(1, 0, 8'hFF));
      dut32.portA.request.put(makeRequestBE(1, 0, 8'hFE));
      dut32.portA.request.put(makeRequestBE(0, 0, ?));
      action
	 let data <- dut32.portA.response.get;
	 $display("%x dut 32", data);
      endaction

      delay(10);
      dut33.portA.request.put(makeRequestBE(2, 8'hFF, 0));
      dut33.portA.request.put(makeRequestBE(1, 8'hFE, 0));
      dut33.portA.request.put(makeRequestBE(0, 8'hFF, ?));
      action
	 let data <- dut33.portA.response.get;
	 $display("%x", data);
      endaction

      delay(10);
      dut34.portA.request.put(makeRequestBE(5, 0, 0));
      dut34.portA.request.put(makeRequestBE(0, 0, ?));
      action
	 let data <- dut34.portA.response.get;
	 $display("%x", data);
      endaction
      
      delay(10); // dut35 addr width 0
      dut35.portA.request.put(makeRequestBE(1, 0, 8'hFF));
      dut35.portA.request.put(makeRequestBE(1, 0, 8'hFE));
      dut35.portA.request.put(makeRequestBE(0, 0, ?));
      action
	 let data <- dut35.portA.response.get;
	 $display("%x dut 35", data);
      endaction

      delay(10);
      dut36.portA.request.put(makeRequestBE(2, 8'hFF, 0));
      dut36.portA.request.put(makeRequestBE(1, 8'hFE, 0));
      dut36.portA.request.put(makeRequestBE(0, 8'hFF, ?));
      action
	 let data <- dut36.portA.response.get;
	 $display("%x", data);
      endaction

      delay(10);// dut35 addr width 0
      dut37.portA.request.put(makeRequestBE(6, 0, 0));
      dut37.portA.request.put(makeRequestBE(0, 0, ?));
      action
	 let data <- dut37.portA.response.get;
	 $display("%x", data);
      endaction


   endseq;
   
   mkAutoFSM(test);

endmodule
