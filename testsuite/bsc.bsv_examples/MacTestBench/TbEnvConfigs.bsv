package TbEnvConfigs;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

import Util::*;
import Randomizeable::*;
import Mac::*;
import SimpleRam::*;
import Control::*;
import RandomSynth::*;

export Configs(..), TbEnvConfigs, TbEnvConfigsStruct(..);
export mkTbEnvConfigs;

////////////////////////////////////////////////////////////////////////////////
/// Set Up Configuration Values
////////////////////////////////////////////////////////////////////////////////

typedef struct {
		MacAddress dut_addr;
		Bool       huge_enable;
		Bit#(32)   bd_offset;
		Bit#(8)    rx_bd_offset;
		Bit#(8)    n_tx_bd;
		Bit#(8)    n_rx_bd;
		UInt#(8)   run_for_n_tx_frames;
		UInt#(8)   run_for_n_rx_frames;
		Bit#(16)   max_frame_len;
		Bit#(32)   txrx_bfr_base;
		} TbEnvConfigsStruct;

typedef Configs#(TbEnvConfigsStruct) TbEnvConfigs;

module mkTbEnvConfigs (TbEnvConfigs);

   Reg#(Bool) initialized <- mkReg(False);

   let offset = 32'h0000_0400;
//   let max_len = 'h0600;
   let max_len = 'h1000;

   Reg#(MacAddress) dut_addr             <- mkRegU;
   Reg#(Bool)       huge_enable          <- mkReg(False);
   Reg#(Bit#(32))   bd_offset            <- mkReg(offset);
   Reg#(Bit#(8))    rx_bd_offset         <- mkReg(0);
   Reg#(Bit#(8))    n_tx_bd              <- mkReg(8);
   Reg#(Bit#(8))    n_rx_bd              <- mkReg(8);
   Reg#(UInt#(8))   run_for_n_tx_frames  <- mkReg(5);
   Reg#(UInt#(8))   run_for_n_rx_frames  <- mkReg(5);
   Reg#(Bit#(16))   max_frame_len        <- mkReg(max_len);
   Reg#(Bit#(32))   txrx_bfr_base        <- mkReg(0);

   Randomize#(MacAddress) addr_gen <- mkRandomizer;
   Randomize#(Bit#(8)) rx_bd_offset_gen <- mkConstrainedRandomizer_Synth(8'h01, 8'h7F);
   Randomize#(Bit#(32)) txrx_bfr_base_gen <- 
   mkConstrainedRandomizer_Synth(0, (32'hFFFF_FFFF - (256 * max_len)));

   rule initialize_finish (!initialized);
      let addr_rand <- addr_gen.next();
      addr_rand[47:46] = 0;
      dut_addr <= addr_rand;

      let rx_bd_offset_rand <- rx_bd_offset_gen.next();
//      rx_bd_offset <= rx_bd_offset_rand;
      rx_bd_offset <= 'h08;

      let txrx_bfr_base_rand <- txrx_bfr_base_gen.next();
      txrx_bfr_base_rand[2:0] = 0;
//      txrx_bfr_base <= txrx_bfr_base_rand;
      txrx_bfr_base <= 'h800;
      
      initialized <= True;
   endrule

   interface Control cntrl;
      method Action init ();
	 addr_gen.cntrl.init();
	 rx_bd_offset_gen.cntrl.init();
	 txrx_bfr_base_gen.cntrl.init();
      endmethod
   endinterface
   
   method _read() if (initialized);
      return TbEnvConfigsStruct {           dut_addr: dut_addr,
				         huge_enable: huge_enable,
				           bd_offset: bd_offset,
				        rx_bd_offset: rx_bd_offset,
				             n_tx_bd: n_tx_bd,
				             n_rx_bd: n_rx_bd,
				 run_for_n_tx_frames: run_for_n_tx_frames,
				 run_for_n_rx_frames: run_for_n_rx_frames,
				       max_frame_len: max_frame_len,
				       txrx_bfr_base: txrx_bfr_base
				 };
   endmethod
   

endmodule

endpackage

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

