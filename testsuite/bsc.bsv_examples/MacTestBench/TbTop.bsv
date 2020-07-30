package TbTop;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

import WBone::*;
import EthTop::*;
import Mii::*;
import GetPut::*;
import ZBus::*;
import Clocks::*;
import FIFO::*;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

interface TbTopIFC;
   interface MiiNibbleTxRxIFC mii_nibble_channel;
   interface WBoneZBusBusIFC master;
   interface WBoneZBusBusIFC slave;
   method Bool int_out();
   (* always_ready, always_enabled *)
   method Action coll_in(Bool value);
   (* always_ready, always_enabled *)
   method Action crs_in(Bool value);
endinterface
      
////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

(* synthesize *)      
module mkTbTop (Clock phy_clk, Reset phy_reset, TbTopIFC ifc);

   EthTop_IFC dut <- eth_top(phy_clk, phy_reset, phy_clk, phy_reset);

   WBoneZBusDualIFC dut_master <-  mkWBoneZBusBuffer;
   WBoneZBusDualIFC dut_slave <-  mkWBoneZBusBuffer;
   
   RWire#(MiiNibble) rx_mii_nibble <- mkRWire(clocked_by(phy_clk), 
					      reset_by(phy_reset));

   Reg#(MiiNibble) rx_nibble <- mkReg(?, clocked_by(phy_clk), 
				      reset_by(phy_reset));

   Reg#(Bool) rx_dv <- mkReg(False, clocked_by(phy_clk), 
			            reset_by(phy_reset));

   // connect all the signals up.
   rule write_connect_slave (!dut.m_wb_stb_o && dut_slave.clientIFC.we.get());

      // WISHBONE common
      let tgd_slv_data_o = dut_slave.clientIFC.dato.get();
      let slv_data_o = tgd_slv_data_o.data;
      dut.wb_dat_i(slv_data_o[31:0]);
      
   endrule

   rule read_connect_slave (!dut.m_wb_stb_o && !dut_slave.clientIFC.we.get() && (dut.wb_err_o() || dut.wb_ack_o()));

      // WISHBONE common
      let slv_data_i = dut.wb_dat_o();
      dut_slave.clientIFC.dati.drive(TaggedData { data: {0, slv_data_i}, tag: 0});
      
   endrule
   

   rule connect_slave_0 (!dut.m_wb_stb_o && (dut.wb_err_o() || dut.wb_ack_o()));

      // WISHBONE common
      dut_slave.clientIFC.err.drive(dut.wb_err_o());
      dut_slave.clientIFC.ack.drive(dut.wb_ack_o());

   endrule

   rule connect_slave_1 (!dut.m_wb_stb_o);

       // WISHBONE slave
      let tgd_address = dut_slave.clientIFC.adr.get();
      let address = tgd_address.data;
      dut.wb_adr_i(address[11:2]);

      let select = dut_slave.clientIFC.sel.get();
      dut.wb_sel_i(select[3:0]);
      dut.wb_we_i(dut_slave.clientIFC.we.get());
      
      let tgd_slv_cyc_o = dut_slave.clientIFC.cyc.get();
      let slv_cyc_o = tgd_slv_cyc_o.data;
      dut.wb_cyc_i(slv_cyc_o);
      dut.wb_stb_i(dut_slave.clientIFC.stb.get());
   endrule
   

   rule write_connect_master (dut.m_wb_stb_o() && dut.m_wb_we_o());

      let mst_data_i = dut.m_wb_dat_o();
      dut_master.clientIFC.dato.drive(TaggedData { data: {0, mst_data_i}, tag: 0});

   endrule

   rule read_connect_master (!dut.m_wb_we_o());
      
      let tgd_mst_data_o = dut_master.clientIFC.dati.get();
      let mst_data_o = tgd_mst_data_o.data;
      dut.m_wb_dat_i(mst_data_o[31:0]);
      
   endrule

   rule connect_master_0 (dut.m_wb_stb_o());

       // WISHBONE master
      let dut_addr_o = dut.m_wb_adr_o();
      dut_master.clientIFC.adr.drive(TaggedData { data: {0, dut_addr_o}, tag: 0});
      
      let dut_sel_o = dut.m_wb_sel_o();
      dut_master.clientIFC.sel.drive({0, dut_sel_o});
      
      dut_master.clientIFC.we.drive(dut.m_wb_we_o());

      let mst_cyc_i = dut.m_wb_cyc_o();
      dut_master.clientIFC.cyc.drive(TaggedData { data: mst_cyc_i, tag: 0});

      dut_master.clientIFC.stb.drive(dut.m_wb_stb_o());

   endrule

   rule connect_master_1;
      
      dut.m_wb_ack_i(dut_master.clientIFC.ack.get());
      dut.m_wb_err_i(dut_master.clientIFC.err.get());
      
   endrule

   rule receive_driven (isValid(rx_mii_nibble.wget()));
      let mii_nibble = validValue(rx_mii_nibble.wget());
      rx_nibble <= mii_nibble;
      rx_dv <= (True);
   endrule

   rule receive_default (!isValid(rx_mii_nibble.wget()));
      rx_nibble <= MiiNibble { nibble: 0, err: False};
      rx_dv <= (False);
   endrule
   
   rule receive_final;
      dut.mrxd_pad_i(rx_nibble.nibble());
      dut.mrxdv_pad_i(rx_dv);
      dut.mrxerr_pad_i(rx_nibble.err());
   endrule
   
   interface MiiNibbleTxRxIFC mii_nibble_channel;
      
      interface Get tx;
	 method ActionValue#(MiiNibble) get if (dut.mtxen_pad_o);
	    let nibble = dut.mtxd_pad_o();
	    let err = dut.mtxerr_pad_o;     
	    return MiiNibble { nibble: nibble, err: err};
	 endmethod
      endinterface
      interface Put rx;
	 method Action put (MiiNibble mii_nibble);
	    rx_mii_nibble.wset(mii_nibble);
	 endmethod
      endinterface
   endinterface

   interface master = dut_master.busIFC;
   interface slave = dut_slave.busIFC;

   method Bool int_out();
      return dut.int_o();
   endmethod
      
   method Action coll_in(Bool value);
      dut.mcoll_pad_i(value);
   endmethod
      
   method Action crs_in(Bool value);
      dut.mcrs_pad_i(value);
   endmethod
      
endmodule

endpackage

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

