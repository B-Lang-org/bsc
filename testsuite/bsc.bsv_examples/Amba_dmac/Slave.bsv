//------------------------------------------------------------------------------
//
//  FILENAME: mkSlave.bsv
//
//  DESCRIPTION: 
//    This bluespec module implements an AMBA AHB Slave.
//
//------------------------------------------------------------------------------

// ( * CLK="HCLK", RSTN="HRESETn" * )

import FIFOF::*;
import ConfigReg::*;
import AhbInterfaces::* ;



typedef bit  [1:0] Status_type;
typedef bit  [1:0] Resp_type;
typedef bit [31:0] Addr_type;
typedef bit [31:0] Data_type;

// Parameterized structure.
typedef struct {
   Bool      read;
   Bool      write;
   Bool      burst;
   Bit#(bsize_width) bsize;
   Bit#(addr_width)  addr;
} Master_req_type #(type bsize_width, type addr_width)  deriving(Bits);



interface Wire_ifc #(type data_type);
   // ----------------------------------------------------------------
   // Wire Interface

   //   Data_type rxd; // rx_data
   //   Bool      rxv; // EN_rx
   //   Bit#(32)  txd;
   //   Bool      txv;

   method Action rx (Data_type d);
   method Action tx;
   method Data_type tx_d;
   method Bool rx_nef(Bool rx_ack);
   method Bool tx_nff;
      
endinterface: Wire_ifc

interface Slave1_ifc  #(type addr_type, type data_type, type resp_type, type status_type);
   interface Slave_ifc#(addr_type, data_type, resp_type, status_type) s;
   interface Wire_ifc#(data_type) rxtx;
endinterface
      

(* synthesize *)
module mkSlave(Slave1_ifc#(Addr_type,Data_type,Resp_type,Status_type));

   Reg#(Bool) s_hready_out_r();
   mkReg#(True) u_s_hready_out_r(s_hready_out_r);

   Reg#(Bool) s_hsel_r();
   mkReg#(False) u_s_hsel_r(s_hsel_r);

   Reg#(Bool) s_hwrite_r();
   mkReg#(False) u_s_hwrite_r(s_hwrite_r);

   Reg#(Bit#(2)) s_htrans_r();
   mkReg#(0) u_s_htrans_r(s_htrans_r);

   Reg#(Addr_type) s_haddr_r();
   mkReg#(0) u_s_haddr_r(s_haddr_r);

   Reg#(Data_type) s_hrdata_r();
   mkReg#(0) u_s_hrdata_r(s_hrdata_r);

   Reg#(Data_type) config0();
   mkReg#(32'h100) u_config0(config0); 

   Reg#(Data_type) config1();
   mkReg#(32'h101) u_config1(config1); 
   Data_type dest_addr = config1;

   ConfigReg#(Data_type) config2();
   mkConfigReg#(32'h102) u_config2(config2); 

   ConfigReg#(Data_type) config3();
   mkConfigReg#(32'h3) u_config3(config3); 

   ConfigReg#(Data_type) config4();
   mkConfigReg#(32'h104) u_config4(config4);

   ConfigReg#(Data_type) config5();  
   mkConfigReg#(32'h105) u_config5(config5);

   ConfigReg#(Data_type) config6(); 
   mkConfigReg#(32'h106) u_config6(config6);


   ConfigReg#(Data_type) config7(); 
   mkConfigReg#(32'h107) u_config7(config7);

   ConfigReg#(Data_type) config8(); 
   mkConfigReg#(32'h108) u_config8(config8);

   FIFOF#(Data_type) rx_fifo ();
   mkSizedFIFOF #(16) u_rx_fifo (rx_fifo);

   FIFOF#(Data_type) tx_fifo ();
   mkSizedFIFOF #(16) u_tx_fifo (tx_fifo);


   Reg#(Data_type) wait_state_cnt();
   mkReg#(5) u_wait_state_cnt(wait_state_cnt);

   rule rl_wait_state (s_hsel_r);
      wait_state_cnt <= (wait_state_cnt==0) ? config3 : wait_state_cnt - 1;
   endrule

   // -----------------------------------------------------------------
   // Slave Methods

      // address phase
      // The address phase always occurs when en_s_hready_in=1.
   interface Slave_ifc s ;
      method hready_in ( s_hsel, s_haddr, s_hwrite, s_htrans);
         action

            s_hsel_r   <= s_hsel;
            s_hwrite_r <= s_hsel && s_hwrite;
            s_haddr_r  <= s_haddr;
            s_htrans_r <= s_htrans;
            
            wait_state_cnt <= config3;

            case (s_haddr[2:0])
               0: begin
                  s_hrdata_r <= rx_fifo.first();
                  if (s_hsel && !s_hwrite && s_htrans>1)
                     rx_fifo.deq();
                  end
               1: s_hrdata_r <= config1;
               2: s_hrdata_r <= config2;
               3: s_hrdata_r <= config3;
               4: s_hrdata_r <= config4;
               5: s_hrdata_r <= config5;
               6: s_hrdata_r <= config6;
               7: s_hrdata_r <= config7;
               default: s_hrdata_r <= 'h0;
            endcase

         endaction
      endmethod

      method write_data (s_hwdata,s_htrans);
         action
            if (s_hwrite_r && s_htrans_r>1) begin
               case (s_haddr_r[2:0])
                  0: config0 <= s_hwdata;    // read rx
                  1: tx_fifo.enq(s_hwdata);  // write tx
                  2: config2 <= s_hwdata;    
                  3: config3 <= s_hwdata;    // programmable wait-state
                  4: config5 <= s_hwdata;   
                  5: config5 <= s_hwdata;
                  6: config6 <= s_hwdata;
                  7: config7 <= s_hwdata;
                  // default: ;
               endcase
            end
         endaction
      endmethod

      method hready_out() if (wait_state_cnt==0);
         return (wait_state_cnt==0);
      endmethod

      method hrdata() if (wait_state_cnt==0);
         return s_hrdata_r;
      endmethod

      method hresp();
         return 2'b00; // Always return OKAY
      endmethod
   endinterface 
   // End Slave Methods
   // -----------------------------------------------------------------


   // ----------------------------------------------------------------
   // Wire Interface
   interface Wire_ifc rxtx ;
      method rx (d);
         action
            rx_fifo.enq(d);
         endaction
      endmethod

      method rx_nef(rx_ack);
         return rx_fifo.notEmpty() && !rx_ack;
      endmethod

      method tx_nff;
         return tx_fifo.notFull();
      endmethod

      method tx;
         action
            tx_fifo.deq();
         endaction
      endmethod

      method tx_d;
         return tx_fifo.first();
      endmethod
   endinterface 
endmodule
