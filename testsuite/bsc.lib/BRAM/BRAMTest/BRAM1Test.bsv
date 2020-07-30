import BRAM::*;
import GetPut::*;
import ClientServer::*;
import StmtFSM::*;
import Clocks::*;

function BRAMRequest#(Bit#(8), Bit#(8)) makeRequest(Bool write, Bit#(8) addr, Bit#(8) data);
   return BRAMRequest{
                      write: write,
                      responseOnWrite : False,
		      address: addr,
		      datain: data
		      };
endfunction

function BRAMRequestBE#(a, d, n) makeRequestBE(Bit#(n) write, a addr, d data);
   return BRAMRequestBE{
			writeen: write,
                        responseOnWrite : False,
			address: addr,
			datain: data
			};
endfunction

(* synthesize *)
module sysBRAM1Test();
   let cfg = defaultValue;
   cfg.allowWriteResponseBypass = False ;
   let cfgLoad = defaultValue;
   cfgLoad.allowWriteResponseBypass = False ;
   cfgLoad.loadFormat = tagged Hex "brams2.txt" ;

   BRAM1Port#(Bit#(8), Bit#(8)) dut0 <- mkBRAM1Server(cfg);
   BRAM1Port#(Bit#(8), Bit#(8)) dut1 <- mkBRAM1Load(False, "bram2.txt");

   BRAM1PortBE#(Bit#(8), Bit#(32), 4) dut2 <- mkBRAM1BE(False);
   BRAM1PortBE#(Bit#(8), Bit#(24), 3) dut3 <- mkBRAM1BELoad(False, "bram2.txt");
   BRAM1PortBE#(Bit#(8), Bit#(16), 2) dut4 <- mkBRAM1BE(False);
   BRAM1PortBE#(Bit#(8), Bit#(8), 1)  dut5 <- mkBRAM1BELoad(False, "bram2.txt");
   
   Stmt test =
   (seq
       delay(10);
       dut1.portA.request.put(makeRequest(False, 0, ?));
       $display("reading[0] = %x", dut1.portA.response.get);
       dut3.portA.request.put(makeRequestBE(0, 7, ?));
       $display("reading[7] = %x", dut3.portA.response.get);
       dut5.portA.request.put(makeRequestBE(0, 4, ?));
       $display("reading[4] = %x", dut5.portA.response.get);
        
       delay(10);
       dut0.portA.request.put(makeRequest(True, 0, 'hFF));
       dut0.portA.request.put(makeRequest(True, 1, 'hFE));
       dut0.portA.request.put(makeRequest(True, 2, 'hFD));
       dut0.portA.request.put(makeRequest(True, 3, 'hFC));
       dut0.portA.request.put(makeRequest(False, 0, ?));
       action 
	  $display("reading[0] = %x", dut0.portA.response.get);
	  dut0.portA.request.put(makeRequest(False, 1, ?));
       endaction
       action 
	  $display("reading[1] = %x", dut0.portA.response.get);
	  dut0.portA.request.put(makeRequest(False, 2, ?));
       endaction
       action 
	  $display("reading[2] = %x", dut0.portA.response.get);
	  dut0.portA.request.put(makeRequest(False, 3, ?));
       endaction
       action 
	  $display("reading[3] = %x", dut0.portA.response.get);
       endaction
       dut0.portA.request.put(makeRequest(True, 8, 'hF8));
       dut0.portA.request.put(makeRequest(False, 8, ?));
       action 
	  $display("reading[8] = %x", dut0.portA.response.get);
	  dut0.portA.request.put(makeRequest(True, 9, 'hF7));
       endaction
       dut0.portA.request.put(makeRequest(False, 9, ?));
       action 
	  $display("reading[9] = %x", dut0.portA.response.get);
	  dut0.portA.request.put(makeRequest(True, 10, 'hF6));
       endaction
       dut0.portA.request.put(makeRequest(False, 10, ?));
       action 
	  $display("reading[10] = %x", dut0.portA.response.get);
       endaction

       dut1.portA.request.put(makeRequest(True, 0, 'hFF));
       dut1.portA.request.put(makeRequest(True, 1, 'hFE));
       dut1.portA.request.put(makeRequest(True, 2, 'hFD));
       dut1.portA.request.put(makeRequest(True, 3, 'hFC));
       dut1.portA.request.put(makeRequest(False, 0, ?));
       action 
	  $display("reading[0] = %x", dut1.portA.response.get);
	  dut1.portA.request.put(makeRequest(False, 1, ?));
       endaction
       action 
	  $display("reading[1] = %x", dut1.portA.response.get);
	  dut1.portA.request.put(makeRequest(False, 2, ?));
       endaction
       action 
	  $display("reading[2] = %x", dut1.portA.response.get);
	  dut1.portA.request.put(makeRequest(False, 3, ?));
       endaction
       action 
	  $display("reading[3] = %x", dut1.portA.response.get);
       endaction
       dut1.portA.request.put(makeRequest(True, 8, 'hF8));
       dut1.portA.request.put(makeRequest(False, 8, ?));
       action 
	  $display("reading[8] = %x", dut1.portA.response.get);
	  dut1.portA.request.put(makeRequest(True, 9, 'hF7));
       endaction
       dut1.portA.request.put(makeRequest(False, 9, ?));
       action 
	  $display("reading[9] = %x", dut1.portA.response.get);
	  dut1.portA.request.put(makeRequest(True, 10, 'hF6));
       endaction
       dut1.portA.request.put(makeRequest(False, 10, ?));
       action 
	  $display("reading[10] = %x", dut1.portA.response.get);
       endaction

       action
	  dut2.portA.request.put(makeRequestBE(4'hF, 0, 'hFF_EE_DD_CC));
	  dut3.portA.request.put(makeRequestBE(3'h7, 0, 'hFF_EE_DD));
	  dut4.portA.request.put(makeRequestBE(2'h3, 0, 'hFF_EE));
	  dut5.portA.request.put(makeRequestBE(1'h1, 0, 'hFF));
       endaction
    
       action
	  dut2.portA.request.put(makeRequestBE(4'hF, 1, 'hBB_AA_99_88));
	  dut3.portA.request.put(makeRequestBE(3'h7, 1, 'hCC_BB_AA));
	  dut4.portA.request.put(makeRequestBE(2'h3, 1, 'hDD_CC));
	  dut5.portA.request.put(makeRequestBE(1'h1, 1, 'hEE));
       endaction
    
       action
	  dut2.portA.request.put(makeRequestBE(0, 0, ?));
	  dut3.portA.request.put(makeRequestBE(0, 0, ?));
	  dut4.portA.request.put(makeRequestBE(0, 0, ?));
	  dut5.portA.request.put(makeRequestBE(0, 0, ?));
       endaction
    
       action
	  dut2.portA.request.put(makeRequestBE(0, 1, ?));
	  dut3.portA.request.put(makeRequestBE(0, 1, ?));
	  dut4.portA.request.put(makeRequestBE(0, 1, ?));
	  dut5.portA.request.put(makeRequestBE(0, 1, ?));
    
	  $display("dut2[0] = %x", dut2.portA.response.get);
	  $display("dut3[0] = %x", dut3.portA.response.get);
	  $display("dut4[0] = %x", dut4.portA.response.get);
	  $display("dut5[0] = %x", dut5.portA.response.get);
       endaction
    
       action
	  $display("dut2[1] = %x", dut2.portA.response.get);
	  $display("dut3[1] = %x", dut3.portA.response.get);
	  $display("dut4[1] = %x", dut4.portA.response.get);
	  $display("dut5[1] = %x", dut5.portA.response.get);
       endaction
    
       // dut2
       dut2.portA.request.put(makeRequestBE(15, 31, 'h11223344));
       dut2.portA.request.put(makeRequestBE(15, 32, 'h55667788));
       dut2.portA.request.put(makeRequestBE(15, 33, 0));
       dut2.portA.request.put(makeRequestBE(15, 34, 0));
       dut2.portA.request.put(makeRequestBE(15, 35, 0));
       dut2.portA.request.put(makeRequestBE(15, 36, 0));
       dut2.portA.request.put(makeRequestBE(15, 37, 0));
       dut2.portA.request.put(makeRequestBE(15, 38, 0));
       dut2.portA.request.put(makeRequestBE(15, 39, 0));
       dut2.portA.request.put(makeRequestBE(15, 40, 0));
       dut2.portA.request.put(makeRequestBE(15, 41, 0));
       dut2.portA.request.put(makeRequestBE(15, 42, 0));
       dut2.portA.request.put(makeRequestBE(15, 43, 0));
       dut2.portA.request.put(makeRequestBE(15, 44, 0));
       dut2.portA.request.put(makeRequestBE(15, 45, 0));


       dut2.portA.request.put(makeRequestBE(1,  31, 'hFF_FE_FD_FC));
       dut2.portA.request.put(makeRequestBE(2,  32, 'hFB_FA_F9_F8));
       dut2.portA.request.put(makeRequestBE(3,  33, 'hF7_F6_F5_F4));
       dut2.portA.request.put(makeRequestBE(4,  34, 'hF3_F2_F1_F0));
       dut2.portA.request.put(makeRequestBE(5,  35, 'hEF_EE_ED_EC));
       dut2.portA.request.put(makeRequestBE(6,  36, 'hEB_EA_E9_E8));
       dut2.portA.request.put(makeRequestBE(7,  37, 'hE7_E6_E5_E4));
       dut2.portA.request.put(makeRequestBE(8,  38, 'hE3_E2_E1_E0));
       dut2.portA.request.put(makeRequestBE(9,  39, 'hDF_DE_DD_DC));
       dut2.portA.request.put(makeRequestBE(10, 40, 'hDB_DA_D9_D8));
       dut2.portA.request.put(makeRequestBE(11, 41, 'hD7_D6_D5_D4));
       dut2.portA.request.put(makeRequestBE(12, 42, 'hD3_D2_D1_D0));
       dut2.portA.request.put(makeRequestBE(13, 43, 'hCF_CE_CD_CC));
       dut2.portA.request.put(makeRequestBE(14, 44, 'hCB_CA_C9_C8));
       dut2.portA.request.put(makeRequestBE(15, 45, 'hC7_C6_C5_C4));
						      
       dut2.portA.request.put(makeRequestBE(0, 31, ?));
       action
	  $display("dut2[31] = %x", dut2.portA.response.get);
	  dut2.portA.request.put(makeRequestBE(0, 32, ?));
       endaction
       action
	  $display("dut2[32] = %x", dut2.portA.response.get);
	  dut2.portA.request.put(makeRequestBE(0, 33, ?));
       endaction
       action
	  $display("dut2[33] = %x", dut2.portA.response.get);
	  dut2.portA.request.put(makeRequestBE(0, 34, ?));
       endaction
       action
	  $display("dut2[34] = %x", dut2.portA.response.get);
	  dut2.portA.request.put(makeRequestBE(0, 35, ?));
       endaction
       action
	  $display("dut2[35] = %x", dut2.portA.response.get);
	  dut2.portA.request.put(makeRequestBE(0, 36, ?));
       endaction
       action
	  $display("dut2[36] = %x", dut2.portA.response.get);
	  dut2.portA.request.put(makeRequestBE(0, 37, ?));
       endaction
       action
	  $display("dut2[37] = %x", dut2.portA.response.get);
	  dut2.portA.request.put(makeRequestBE(0, 38, ?));
       endaction
       action
	  $display("dut2[38] = %x", dut2.portA.response.get);
	  dut2.portA.request.put(makeRequestBE(0, 39, ?));
       endaction
       action
	  $display("dut2[39] = %x", dut2.portA.response.get);
	  dut2.portA.request.put(makeRequestBE(0, 40, ?));
       endaction
       action
	  $display("dut2[40] = %x", dut2.portA.response.get);
	  dut2.portA.request.put(makeRequestBE(0, 41, ?));
       endaction
       action
	  $display("dut2[41] = %x", dut2.portA.response.get);
	  dut2.portA.request.put(makeRequestBE(0, 42, ?));
       endaction
       action
	  $display("dut2[42] = %x", dut2.portA.response.get);
	  dut2.portA.request.put(makeRequestBE(0, 43, ?));
       endaction
       action
	  $display("dut2[43] = %x", dut2.portA.response.get);
	  dut2.portA.request.put(makeRequestBE(0, 44, ?));
       endaction
       action
	  $display("dut2[44] = %x", dut2.portA.response.get);
	  dut2.portA.request.put(makeRequestBE(0, 45, ?));
       endaction
       action
	  $display("dut2[45] = %x", dut2.portA.response.get);
       endaction
       
       // dut3 
       dut3.portA.request.put(makeRequestBE(7, 31, 0));
       dut3.portA.request.put(makeRequestBE(7, 32, 0));
       dut3.portA.request.put(makeRequestBE(7, 33, 0));
       dut3.portA.request.put(makeRequestBE(7, 34, 0));
       dut3.portA.request.put(makeRequestBE(7, 35, 0));
       dut3.portA.request.put(makeRequestBE(7, 36, 0));
       dut3.portA.request.put(makeRequestBE(7, 37, 0));


       dut3.portA.request.put(makeRequestBE(1,  31, 'hFF_FE_FD));
       dut3.portA.request.put(makeRequestBE(2,  32, 'hFB_FA_F9));
       dut3.portA.request.put(makeRequestBE(3,  33, 'hF7_F6_F5));
       dut3.portA.request.put(makeRequestBE(4,  34, 'hF3_F2_F1));
       dut3.portA.request.put(makeRequestBE(5,  35, 'hEF_EE_ED));
       dut3.portA.request.put(makeRequestBE(6,  36, 'hEB_EA_E9));
       dut3.portA.request.put(makeRequestBE(7,  37, 'hE7_E6_E5));
						      
       dut3.portA.request.put(makeRequestBE(0, 31, ?));
       action
	  $display("dut3[31] = %x", dut3.portA.response.get);
	  dut3.portA.request.put(makeRequestBE(0, 32, ?));
       endaction
       action
	  $display("dut3[32] = %x", dut3.portA.response.get);
	  dut3.portA.request.put(makeRequestBE(0, 33, ?));
       endaction
       action
	  $display("dut3[33] = %x", dut3.portA.response.get);
	  dut3.portA.request.put(makeRequestBE(0, 34, ?));
       endaction
       action
	  $display("dut3[34] = %x", dut3.portA.response.get);
	  dut3.portA.request.put(makeRequestBE(0, 35, ?));
       endaction
       action
	  $display("dut3[35] = %x", dut3.portA.response.get);
	  dut3.portA.request.put(makeRequestBE(0, 36, ?));
       endaction
       action
	  $display("dut3[36] = %x", dut3.portA.response.get);
	  dut3.portA.request.put(makeRequestBE(0, 37, ?));
       endaction
       action
	  $display("dut3[37] = %x", dut3.portA.response.get);
       endaction

       // dut4
       dut4.portA.request.put(makeRequestBE(3, 31, 0));
       dut4.portA.request.put(makeRequestBE(3, 32, 0));
       dut4.portA.request.put(makeRequestBE(3, 33, 0));

       dut4.portA.request.put(makeRequestBE(1,  31, 'hFF_FE));
       dut4.portA.request.put(makeRequestBE(2,  32, 'hFB_FA));
       dut4.portA.request.put(makeRequestBE(3,  33, 'hF7_F6));
						      
       dut4.portA.request.put(makeRequestBE(0, 31, ?));
       action
	  $display("dut4[31] = %x", dut4.portA.response.get);
	  dut4.portA.request.put(makeRequestBE(0, 32, ?));
       endaction
       action
	  $display("dut4[32] = %x", dut4.portA.response.get);
	  dut4.portA.request.put(makeRequestBE(0, 33, ?));
       endaction
       action
	  $display("dut4[33] = %x", dut4.portA.response.get);
       endaction

       // dut5
       dut5.portA.request.put(makeRequestBE(1, 31, 0));


       dut5.portA.request.put(makeRequestBE(1,  31, 'hFF));
						      
       dut5.portA.request.put(makeRequestBE(0, 31, ?));
       action
	  $display("dut5[31] = %x", dut5.portA.response.get);
       endaction
    
    
       delay(100);
    endseq);
   
   mkAutoFSM(test);
   
endmodule
