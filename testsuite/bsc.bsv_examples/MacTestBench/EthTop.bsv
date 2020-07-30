////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

package EthTop;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

interface EthTop_IFC;

   // WISHBONE common
   method Action   wb_dat_i(Bit#(32) value);  // WISHBONE data input
   method Bit#(32) wb_dat_o();                // WISHBONE data output
   method Bool     wb_err_o();                // WISHBONE error output
          
   // WISHBONE slave
   method Action   wb_adr_i(Bit#(10) value);  // WISHBONE address input
   method Action   wb_sel_i(Bit#(4) value);   // WISHBONE byte select input
   method Action   wb_we_i(Bool value);       // WISHBONE write enable input
   method Action   wb_cyc_i(Bool value);      // WISHBONE cycle input
   method Action   wb_stb_i(Bool value);      // WISHBONE strobe input
   method Bool     wb_ack_o();                // WISHBONE acknowledge output
      
   // WISHBONE master
   method Bit#(32) m_wb_adr_o;
   method Bit#(4)  m_wb_sel_o;
   method Bool     m_wb_we_o;
   method Action   m_wb_dat_i(Bit#(32) value);
   method Bit#(32) m_wb_dat_o();
   method Bool     m_wb_cyc_o;
   method Bool     m_wb_stb_o;
   method Action   m_wb_ack_i(Bool value);
   method Action   m_wb_err_i(Bool value);
      
   // Tx
   method Bit#(4)  mtxd_pad_o;                // Transmit nibble (to PHY)
   method Bool     mtxen_pad_o;               // Transmit enable (to PHY)
   method Bool     mtxerr_pad_o;              // Transmit error (to PHY)

   // Rx
   method Action   mrxd_pad_i(Bit#(4) value); // Receive nibble (from PHY)
   method Action   mrxdv_pad_i(Bool value);   // Receive data valid (from PHY)
   method Action   mrxerr_pad_i(Bool value);  // Receive data error (from PHY)
      
   // Common Tx and Rx
   method Action   mcoll_pad_i(Bool value);   // Collision (from PHY)
   method Action   mcrs_pad_i(Bool value);    // Carrier sense (from PHY)
      
   // MII Management interface
   method Action   md_pad_i;		      // MII data input (from I/O cell)
   method Bool     mdc_pad_o;                 // MII Management data clock (to PHY)
   method Bool     md_pad_o;                  // MII data output (to I/O cell)
   method Bool     md_padoe_o;                // MII data output enable (to I/O cell)
      
   method Bool     int_o;                     // Interrupt output
      
endinterface

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////


 
import "BVI" eth_top =
module eth_top(Clock rx_clk, Reset rx_reset, Clock tx_clk, Reset tx_reset, EthTop_IFC ifc);

   default_clock clk (wb_clk_i);
   default_reset rst (wb_rst_n_i);
   
   input_clock tx_clk(mtx_clk_pad_i) = tx_clk;
   input_clock rx_clk(mrx_clk_pad_i) = rx_clk;
   
   // WISHBONE common
   method  wb_dat_i(wb_dat_i)           enable((* inhigh *)EN1);  // WISHBONE data input
   method  (* reg *) wb_dat_o wb_dat_o();                        // WISHBONE data output
   method  (* reg *) wb_err_o wb_err_o();                        // WISHBONE error output

      
   // WISHBONE slave
   method  wb_adr_i(wb_adr_i)           enable((* inhigh *)EN2);  // WISHBONE address input
   method  wb_sel_i(wb_sel_i)           enable((* inhigh *)EN3);  // WISHBONE byte select input
   method  wb_we_i(wb_we_i)             enable((* inhigh *)EN4);  // WISHBONE write enable input
   method  wb_cyc_i(wb_cyc_i)           enable((* inhigh *)EN5);  // WISHBONE cycle input
   method  wb_stb_i(wb_stb_i)           enable((* inhigh *)EN6);  // WISHBONE strobe input
   method  (* reg *) wb_ack_o wb_ack_o();                        // WISHBONE acknowledge output
      
   // WISHBONE master
   method  (* reg *) m_wb_adr_o m_wb_adr_o();
   method  (* reg *) m_wb_sel_o m_wb_sel_o();
   method  (* reg *) m_wb_we_o m_wb_we_o();
   method  m_wb_dat_i(m_wb_dat_i)       enable((* inhigh *)EN7);
   method  (* reg *) m_wb_dat_o m_wb_dat_o();
   method  (* reg *) m_wb_cyc_o m_wb_cyc_o();
   method  (* reg *) m_wb_stb_o m_wb_stb_o();
   method  m_wb_ack_i(m_wb_ack_i)       enable((* inhigh *)EN8);
   method  m_wb_err_i(m_wb_err_i)       enable((* inhigh *)EN9);

   // Tx
   method  (* reg *) mtxd_pad_o mtxd_pad_o()                   clocked_by(tx_clk) reset_by(no_reset); // Transmit nibble (to PHY)
   method  (* reg *) mtxen_pad_o mtxen_pad_o()                 clocked_by(tx_clk) reset_by(no_reset); // Transmit enable (to PHY)
   method  (* reg *) mtxerr_pad_o mtxerr_pad_o()               clocked_by(tx_clk) reset_by(no_reset); // Transmit error (to PHY)

   // Rx
   method   mrxd_pad_i(mrxd_pad_i)      enable((* inhigh *)EN10) clocked_by(rx_clk) reset_by(no_reset); // Receive nibble (from PHY)
   method   mrxdv_pad_i(mrxdv_pad_i)    enable((* inhigh *)EN11) clocked_by(rx_clk) reset_by(no_reset); // Receive data valid (from PHY)
   method   mrxerr_pad_i(mrxerr_pad_i)  enable((* inhigh *)EN12) clocked_by(rx_clk) reset_by(no_reset); // Receive data error (from PHY)

   // Common Tx and Rx
   method   mcoll_pad_i(mcoll_pad_i)    enable((* inhigh *)EN13)  clocked_by(rx_clk) reset_by(no_reset); // Collision (from PHY)
   method   mcrs_pad_i(mcrs_pad_i)      enable((* inhigh *)EN14)  clocked_by(rx_clk) reset_by(no_reset); // Carrier sense (from PHY)


   // MII Management interface
   method   md_pad_i()			enable(md_pad_i);	 // MII data input (from I/O cell)
   method  (* reg *) mdc_pad_o mdc_pad_o();                      // MII Management data clock (to PHY)
   method  (* reg *) md_pad_o md_pad_o();                        // MII data output (to I/O cell)
   method  (* reg *) md_padoe_o md_padoe_o();                    // MII data output enable (to I/O cell)

   method  (* reg *) int_o int_o();                              // Interrupt output

   schedule 
      (m_wb_ack_i,
       m_wb_dat_i,
       m_wb_err_i,
       mcoll_pad_i,
       mcrs_pad_i,
       md_pad_i,
       mrxd_pad_i,
       mrxdv_pad_i,
       mrxerr_pad_i,
       wb_adr_i,
       wb_cyc_i,
       wb_dat_i,
       wb_sel_i,
       wb_stb_i,
       wb_ack_o,
       wb_we_i,
       wb_dat_o,
       wb_err_o,
       m_wb_adr_o,
       m_wb_sel_o,
       m_wb_we_o,
       m_wb_dat_o,
       m_wb_cyc_o,
       m_wb_stb_o,
       mtxd_pad_o,
       mtxen_pad_o,
       mtxerr_pad_o,
       mdc_pad_o,
       md_pad_o,
       md_padoe_o,
       int_o) CF
      (m_wb_ack_i,
       m_wb_dat_i,
       m_wb_err_i,
       mcoll_pad_i,
       mcrs_pad_i,
       md_pad_i,
       mrxd_pad_i,
       mrxdv_pad_i,
       mrxerr_pad_i,
       wb_adr_i,
       wb_cyc_i,
       wb_dat_i,
       wb_sel_i,
       wb_stb_i,
       wb_ack_o,
       wb_we_i,
       wb_dat_o,
       wb_err_o,
       m_wb_adr_o,
       m_wb_sel_o,
       m_wb_we_o,
       m_wb_dat_o,
       m_wb_cyc_o,
       m_wb_stb_o,
       mtxd_pad_o,
       mtxen_pad_o,
       mtxerr_pad_o,
       mdc_pad_o,
       md_pad_o,
       md_padoe_o,
       int_o);

endmodule


endpackage

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////
