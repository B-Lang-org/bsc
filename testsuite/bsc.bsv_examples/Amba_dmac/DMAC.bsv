//------------------------------------------------------------------------------
//
//  FILENAME: mkDMAC.bsv
//
//  DESCRIPTION: 
//    This bluespec module implements a DMA Controller.
//
//------------------------------------------------------------------------------
// 
//
//
//The Bluespec AMBA DMAC supports the following features.
//- Incrementing Address Transfers
//  Typically used for moving to/from memory
//- Non-increment Address Transfers
//  Typically used for moving to/from peripherals
//
//- Ring-Buffer Support
//   
//- Programmable Burst Size range from 1-16 Words
//   - The burst size can be configured from 1 to 16 words per
//     burst.  If the source and destination peripherals burst
//     sizes are not equal then the smaller of the two should be
//     programmed into the dma.
//   
//- Peripheral Rate control via external control inputs
//   - Rate control from a source peripheral can be throttled via
//     the discrete signals src_ef and src_aef.  src_ef indicates
//     the source fifo is empty.  src_ef=0 indicates that at least
//     one word is available for transfer.  src_aef indicates that 
//     the source fifo is almost empty.  src_aef=0 indicates that
//     the source fifo contains at least one burst of data.
//     
//   - Rate control to the destination peripheral can be throttled 
//     via the discrete signals dest_ff and dest_aff.  dest_ff
//     indicates that the destination fifo is full.  dest_ff=0 
//     indicates that the destination fifo has room for at least
//     one word.  dest_aff indicates that the destination fifo is
//     almost full.  dest_aff=0 indicates that the destination fifo
//     has enough room for at least one burst.
//
//- Maskable Interrupts for
//   - Transfer Count Reached
//     An Transfer Count interrupt is generated when the number of 
//     words transferred reaches a programmable threshold.     
//     
//   - Destination Ring Buffer Almost Full
//     An Almost Full interrupt is generated when the Destination 
//     Ring Buffer is Almost Full.  This interrupt typically indicates 
//     a peripheral has provided enough data for the processor to work 
//     on.  The Almost Full Threshold is programmable.  When set to the 
//     size of the ring buffer, this interrupt indicates fifo full.
//     
//   - Source Ring Buffer Almost Empty
//     An Almost Empty interrupt is generated when the Source Ring 
//     Buffer becomes almost empty.  This interrupt typical indicates 
//     that a peripheral has is ready, or will soon be ready for more 
//     data.  The Almost Empty Threshold is programmable.  When the  
//     threshold is set to zero the interrupt will fire when the Source 
//     Ring Buffer becomes empty.
//     
//   - Timeout
//     An interrupt is generated when a programmable timeout limit 
//     is reached, indicating that some, but less than Transfer Count, 
//     data has been transfered. 
//
//   - AMBA Bus Error
//     A bus error interrupt is generate when a bus error is detected.
//
// Overview
// The Bluespec AMBA DMAC (BADMAC) shall consist of an AMBA Slave 
// Interface, an AMBA Master Interface, a Peripheral Status Interface, 
// and the BADMAC logic.
//
// Functional Requirements
//
// 1. AMBA Slave Interface (AHBS)
//    The BADMAC shall receive receive configuration via the Slave 
//    Interface, typically from the processor.
//
// 2. AMBA Master Interface (AHBM)
//    The BADMAC shall perform the data move operations via the
//    Master Interface.
//    The methods between the AHBM and the controller are:
//       master_burst_read_req
//       master_burst_write_req
//       master_single_read_req
//       master_single_write_req
//
// 3. Peripheral Status Interface (PSI)
//    The BADMAC shall used the Peripheral Status Interface to obtain 
//    status from the source and destination peripherals.  These signals 
//    correspond to common FIFO Flags
//
//    ef_s  - When low indicates the source has at least 1 word of data 
//            available to be read.
//    aef_s - When low indicates the source has at least 1 burst of data 
//            available to be read.
//    ff_d  - When low indicates the destination has space available for 
//            at least 1 word of data
//    aff_d - When low indicates the destination has space available for 
//            at least 1 burst of data (!AFF)
//
// 4.  Addressing Modes
// 4.1 Memory Mode
//     When in Memory Mode the BADMAC shall increment the address after 
//     every word.  When the address reaches max_addr (a programmable 
//     register) the BADMAC shall wrap the address back to min_addr (a
//     programmable register).
//
// 4.2 Peripheral Mode
//     When in Peripheral Mode the BADMAC maintain the address at its
//     current value.
//
// 5.  Data Transfer Control
//     The BADMAC shall initiate a transfer when the GO bit is set. When
//     in Peripheral Mode the BADMAC shall throttle the data transfer rate 
//     using the PSI status signals.  When in Memory Mode the BADMAC shall
//     throttle the data transfer rate based upon stop_addr (a programmable
//     register).  The BADMAC shall support one-shot mode and repetitive
//     mode.  When in one-shot mode the BADMAC shall transfer the amount of
//     data defined in transfer_size (a programmable register) and then
//     stop.  When in repetitive mode the BADMAC shall reset the internal
//     counter (transfer_cnt) and shall continue to move data.
//
// 6.  Interrupts
//     The BADMAC interrupts shall be maskable.  The BADMAC shall generate
//     an interrupt upon the following conditions.
//       - Transfer Count Reached
//         The BADMAC shall generate an interrupt when the number of bytes 
//         defined in transfer_size ( a programmable register) has been 
//         transferred.
//       - Ring Buffer Threshold Reached
//         The BADMAC shall generate an interrupt when there is sufficient
//         data in the Ring Buffer defined by:
//           |current_addr-stop_addr| > int_thresh
//       - Timeout
//         The BADMAC shall generate an interrupt when data has been 
//         moved since the last interrupt and the time since the last
//         interrupt exceeds a programmable threshold.
//       - AMBA Error
//

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


// ====================================================================================


interface Dmac_ifc #(type addr_type, type data_type, type resp_type, type status_type);

   interface Slave_DMAC_ifc#(addr_type, data_type,resp_type, status_type) s ;

   interface Master_ifc#(addr_type, data_type,resp_type, status_type) m;


   // ----------------------------------------------------------------
   // Flow Control Interface

      method Action m_src_rdy(Bit#(16) src_rdy);
      method Action m_dest_rdy(Bit#(16) src_rdy);

      method Bit#(16) src_ack();
      
      method Bit#(16) dest_ack();
      

   // End Flow Control Interface
   // ----------------------------------------------------------------

      // The external interrupt signal is connected to the 
      // implicit interrupt.rdy signal.
      method Bool interrupt;
                         
   // htrans[1:0]  // from master to slave 0=idle, 1=busy, 2=noseq, 3=seq
   // haddr[31:0]  // from master to slave
   // hburst[2:0]  // from master to slave 
   //    0 = single, 1=incr, 2=wrap4, 3=incr4, 4=wrap8, 5=incr8, 6=wrap16, 7=incr16
   // hwdata[31:0] // from master to slave
   // hwrite       // from master to slave 1=write, 0=read
   // hsize[2:0]   // from master to slave 
   //    0=byte, 1=hword, 2=word, 3=64bit, 4=4word, 5=8word, 6=512bit, 7=1024bit
   // hprot[3:0]   // from master to slave
   //    [3]=cacheable, [2]=bufferable, [1]=privileged, [0]=data{1}/opcode(0)
   // hsel         // to slave
   // hready_in    // selected hready of the bus.
   // hready_out   // from slave 
   // hresp[1:0]   // from slave 0=okay, 1=error, 2=retry, 3=split

   // every slave is required to have at least 1KByte of address haddr[9:0]
   // bus master shall not perform an incrementing transfer across a 1K boundary

     
endinterface

(* synthesize *)
module mkDMAC(Dmac_ifc#(Addr_type,Data_type,Resp_type,Status_type));


   int state_idle = 0;
   int state_transfer = 1;

   Reg#(Bool) s_hready_out_r();
   mkReg#(False) u_s_hready_out_r(s_hready_out_r);

   Reg#(Bool) s_hsel_r();
   mkReg#(False) u_s_hsel_r(s_hsel_r);

   Reg#(Bool) s_hwrite_r();
   mkReg#(False) u_s_hwrite_r(s_hwrite_r);

   Reg#(Addr_type) s_haddr_r();
   mkReg#(0) u_s_haddr_r(s_haddr_r);

   Reg#(Data_type) s_hrdata_r();
   mkReg#(0) u_s_hrdata_r(s_hrdata_r); 

   Reg#(Data_type) config0();
   mkReg#(0) u_config0(config0); // src_address
   Data_type src_addr = config0;
   
   Reg#(Data_type) config1();
   mkReg#(0) u_config1(config1); // dest_address
   Data_type dest_addr = config1;

   ConfigReg#(Data_type) config2();
   mkConfigReg#(0) u_config2(config2); // number of bytes to transfer
   Data_type transfer_cnt = config2;

   ConfigReg#(Data_type) config3();
   mkConfigReg#(32'hFFFF_FFFF) u_config3(config3); // Interrupt Enable

   ConfigReg#(Data_type) config4();
   mkConfigReg#(32'h0) u_config4(config4); // Interrupt clear

   ConfigReg#(Data_type) config5();  // Interrupt Status
   mkConfigReg#(0) u_config5(config5);
   Bit#(32) transfer_done = 0; // transfer done
   Bit#(32) src_to        = 1; // destination timeout
   Bit#(32) dest_to       = 2; // source timeout
   Bit#(32) error_code    = 3; // response error code detected

   
   ConfigReg#(Data_type) config6(); // source configuration 
   mkConfigReg#(32'h1) u_config6(config6); 
   Int#(10) src_step    = unpack(config6[9:0]);
   Bit#(4)  src_sel     = config6[15:12];
   Bool     src_rdy_en  = unpack(config6[16]);
   
   
   ConfigReg#(Data_type) config7(); // destination configuration
   mkConfigReg#(32'h2) u_config7(config7); 
   Int#(10) dest_step   = unpack(config7[9:0]);
   Bit#(4)  dest_sel    = config7[15:12];
   Bool     dest_rdy_en = unpack(config7[16]); 

   ConfigReg#(Data_type) config8(); // timeout value
   mkConfigReg#('h100) u_config8(config8);
   Data_type timeout = config8;

   ConfigReg#(Data_type) config9(); // mode configuration
   mkConfigReg#('h100) u_config9(config9);
   Bit#(5)  mode       = config9[4:0];
   Bool     normal     = mode==0;
   Bool     fill       = mode==1;
   Bool     fill_incr  = mode==2;
   Bit#(10) burst_size = config9[17:8];
   
   ConfigReg#( Bit#(10) ) burst_cnt();
   mkConfigReg#(0) u_burst_cnt(burst_cnt);

   ConfigReg#(Data_type) config10(); // fill value
   mkConfigReg#('h100) u_config10(config10);
   Data_type fill_value = config10;

   ConfigReg#(Data_type) to_cnt();
   mkReg#(32'h100) u_to_cnt(to_cnt);

   Reg#(Data_type) s_hwdata_r();
   mkReg#(0) u_s_hwdata_r(s_hwdata_r); 

   Reg#(Bool)    m_hgrant_r();
   mkReg#(False) u_m_hgrant_r(m_hgrant_r);

   Reg#(Bit#(2)) m_htrans_r();
   mkReg#(0) u_m_htrans_r(m_htrans_r);

   Reg#(int) m_state();
   mkReg#(0) u_m_state(m_state);

   ConfigReg#(Bool)    m_dest_rdy_r();
   mkConfigReg#(False) u_m_dest_rdy_r(m_dest_rdy_r);
   
   ConfigReg#(Bool)    m_src_rdy_r();
   mkConfigReg#(False) u_m_src_rdy_r(m_src_rdy_r);

   Reg#(Addr_type) m_haddr_r();
   mkReg#(0) u_m_haddr_r(m_haddr_r);

   Reg#(Bool)    m_hwrite_r();
   mkReg#(False) u_m_hwrite_r(m_hwrite_r);

   FIFOF#(Data_type) dma_fifo ();
   mkSizedFIFOF #(16) u_dma_fifo (dma_fifo);

   ConfigReg#(Bool)    load_transfer_cnt_r();
   mkConfigReg#(False) u_load_transfer_cnt_r(load_transfer_cnt_r);

   Reg#(Bool)    m_hread_r();
   mkReg#(False) u_m_hread_r(m_hread_r);

   Reg#(Bool)    enq();
   mkReg#(False) u_enq(enq);

   Reg#(Bool)    deq();
   mkReg#(False) u_deq(deq);

   Reg#(Bool)    fill_r();
   mkReg#(False) u_fill_r(fill_r);

   Reg#(Bit#(4)) fifo_cnt();
   mkReg#(0) u_fifo_cnt(fifo_cnt);

   Reg#(Bool)    do_fill_enq_r();
   mkReg#(False) u_do_fill_enq_r(do_fill_enq_r);





   // ----------------------------------------------------------------
   // DMA STATE MACHINE

   // In state idle(0) the state machine (sm) waits for the source to have 
   // data (m_src_rdy_r) and the destination to have room (m_dest_rdy_r). 
   // Note, in this design the dma_fifo is guaranteed to be empty.  If 
   // the design changes and the fifo needs to be monitored then 
   // dma_fifo.notEmpty() and dma_fifo.notFull() would be used.  When
   // the above conditions are met the sm asserts the bus request (m_hbusreq)
   // and transitions to state read_req(1).

      rule idle (m_state==state_idle && transfer_cnt!=0 && m_src_rdy_r && m_dest_rdy_r);
         m_state <= state_transfer;
         burst_cnt <= burst_size;
      endrule
      

      rule to (m_state==state_idle && transfer_cnt!=0 && to_cnt!=0);

         to_cnt <= to_cnt-1;
         config5 <= {config5[31:3], 
                     pack(!m_dest_rdy_r && transfer_cnt==1),
                     pack(!m_src_rdy_r && transfer_cnt==1),
                     config5[0]};
      endrule
      
      rule to_reset ( m_state==state_idle && (transfer_cnt==0 || m_src_rdy_r && m_dest_rdy_r));
         to_cnt <= config8;
      endrule

      
   // While in state read_req(1) the sm waits for the bus arbiter to grant
   // the bus.  When the bus is granted the sm drives the address bus, drives
   // hwrite=0 and transisitions to state read_addr_phase(2).  Note, a rule
   // does not exist for this state because the state is handled entirely by 
   // action method m_hgrant.
   
   // The sm remains in state read_addr_phase(2) until m_hready is asserted,
   // and then transitions to read_data_phase(3).  Again, a rule doesn't
   // exist for this state because action method m_hready handles it.
      
   // The sm remains in state read_data_phase(3) until m_hready is asserted,
   // and then enqueues the data into the dma_fifo, asserts bus request for the
   // write phase and transitions to write_req(4).  This state is also handled by
   // method m_hready.
   
   // The sm remains in state write_req(4) until m_hgrant fires and then drives
   // the destination address onto the bus, asserts the write strobe (m_hwrite=0)
   // and transitions to the write_addr_phase(5).  This state is handled by method
   // m_hgrant.

   // The sm remains in state write_addr_phase(5) until m_hready is asserted,
   // and then transitions to write_data_phase(6).  Again, a rule doesn't
   // exist for this state because action method m_hready handles it.
      
   // The sm remains in state write_data_phase(6) until m_hready is asserted,
   // and then dequeues the data from the dma_fifo, and returns to state idle.  
   // This state is also handled by method m_hready.

   // -----------------------------------------------------------------
   interface Slave_DMAC_ifc s;
   // Slave Methods   
      // address phase
      // The address phase allows occurs when en_s_hready_in=1.
      
      method hready_in ( s_hsel, s_haddr, s_hwrite);
         action
            s_hsel_r   <= s_hsel;
            s_hwrite_r <= s_hsel && s_hwrite;
            s_haddr_r  <= s_haddr;

            if (s_hsel) begin
               case (s_haddr)
                  0: s_hrdata_r <= config0;
                  1: s_hrdata_r <= config1;
                  2: s_hrdata_r <= config2;
                  3: s_hrdata_r <= config3;
                  4: s_hrdata_r <= config4;
                  5: s_hrdata_r <= config5;
                  6: s_hrdata_r <= config6;
                  7: s_hrdata_r <= config7;
                  8: s_hrdata_r <= config8;
                  9: s_hrdata_r <= config9;
                  10:s_hrdata_r <= config10;
                  default: s_hrdata_r <= 'h0;
               endcase        
               s_hready_out_r <= True; // 0 wait-state
            end            
         endaction
      endmethod

      method write_data (s_hwdata);
         action
            if (s_hwrite_r) begin
               s_hwdata_r <= s_hwdata;
               case (s_haddr_r)
                  0: config0 <= s_hwdata;
                  1: config1 <= s_hwdata;
                  2: config2 <= s_hwdata; // transfer count
                  3: config3 <= s_hwdata;
                  4: config5 <= s_hwdata & config5; // interrupt clear
                  5: config5 <= s_hwdata;
                  6: config6 <= s_hwdata;
                  7: config7 <= s_hwdata;
                  8: config8 <= s_hwdata;
                  9: config9 <= s_hwdata;
                  10:config10 <= s_hwdata;
                  default: $display("WARNING: Invalid Slave Address");
               endcase
            end
         endaction
      endmethod
      
      method hready_out() if (s_hready_out_r);
         return True;
      endmethod
      
      method hrdata() if (s_hready_out_r);
         return s_hrdata_r;
      endmethod
      
      method hresp();
         return 2'b00; // Always return OKAY
      endmethod
      
   // End Slave Methods
   endinterface 
   // -----------------------------------------------------------------

   interface Master_ifc m;
      method master (hrdata, hgrant, hresp) if (m_state==state_transfer && m_dest_rdy_r &&
                                                (m_src_rdy_r || dma_fifo.notEmpty() || m_hread_r || enq) );
                                                
         action
            Bool early_deq    = hgrant && m_state==state_transfer && dma_fifo.notEmpty();
            Bool err_detect   = hresp==2'b01;
            Bool dest_timeout = False;
            Bool src_timeout  = False;
            Bool xfer_done    = transfer_cnt==0 ;
            Bool do_write     = hgrant && m_state==state_transfer && fifo_cnt!=0;
            Bool do_read      = hgrant && m_state==state_transfer && fifo_cnt==0 && 
                                transfer_cnt!=0 && !fill_r && m_src_rdy_r && 
                                config5==0 && burst_cnt!=0;
                                
            Bool do_fill_enq  = fill_r && transfer_cnt!=0 && dma_fifo.notFull();
            
            Data_type config5_din = {config5[31:4],pack(err_detect),pack(dest_timeout),pack(src_timeout),pack(xfer_done)};
            
            
            do_fill_enq_r <= do_fill_enq;
            
            fill_r <= fill || fill_incr;

            // STATE READ_DATA_PHASE(3)
            // Enqueue data into fifo and transition from state 
            // read_data_phase to write_req when hready asserts/fires. Also
            // assert bus request (hbusreq) for the next write phase.

            if (m_state==state_transfer) begin 

               // Set interrupts
               config5 <= config5_din | config5;
                      
               // return to idle on interrupt        
               if (config5_din!=0 && !dma_fifo.notEmpty() && !m_hread_r && !enq) begin
                  m_state <= state_idle;
               end

               if (!src_rdy_en) 
                  burst_cnt <= 1;
               else if ((burst_cnt==0 || burst_cnt==burst_size) && !m_src_rdy_r)
                  burst_cnt <= burst_size; // burst_size = config9[17:8]
               else if ( (fill_r || do_read) && burst_cnt!=0) begin
                  burst_cnt <= burst_cnt - 1;
               end
               
            end

            if (enq && fifo_cnt==0 || do_fill_enq && fifo_cnt==0)
               fifo_cnt <= fifo_cnt + 1;
            else if (!enq && !do_fill_enq && fifo_cnt!=0) begin
               fifo_cnt <= fifo_cnt - 1;
            end
            
            if (do_read) begin
               config0 <= config0+pack(zeroExtend(src_step));
            end

            if (do_write) begin
               config1 <= config1+pack(zeroExtend(dest_step));
            end
               

            m_haddr_r  <= do_write ? dest_addr : src_addr;
            
            m_hwrite_r <= do_write;
            deq <= m_hwrite_r;
            if (deq) begin
               dma_fifo.deq();
            end

            if (config5_din!=0)
               config2 <= 0; // clear on interrupt
            else if (do_fill_enq || do_read) begin 
               config2 <= transfer_cnt - 1;  // decrement transfer_cnt;
            end

            m_hread_r <= do_read; 
            enq <= m_hread_r;
            if (enq) 
               dma_fifo.enq(hrdata);
            else if (do_fill_enq) begin
               dma_fifo.enq(fill_value);
               if (fill_incr) config10 <= fill_value + 1;
            end
                        
            if (do_write || do_read) begin
               m_htrans_r <= 2'b10;
            end
            else begin
               m_htrans_r <= 2'b00;
            end
                           
         endaction
      endmethod

      method htrans;
         return m_htrans_r;
      endmethod

      
      // always drives the next value in the fifo      
      method hwdata;
         return dma_fifo.first();
      endmethod
      
      // always drives the address
      method haddr;
         return m_haddr_r;
      endmethod
      
      // always drives the hwrite signal
      method hwrite;
         return m_hwrite_r;
      endmethod

   endinterface

   // End Master Interface
   // ----------------------------------------------------------------

      method interrupt;
         return ((config5 & config3)!=0 && m_state==state_idle);
      endmethod
      


   // -----------------------------------------------------------------
   // Flow Control Methods


      // selects 1 of 16 source rdy lines.  src_rdy indicates that the
      // source has data to send (not empty).
      
      method Action m_src_rdy(Bit#(16) src_rdy);
            m_src_rdy_r <= unpack(src_rdy[src_sel]) || !src_rdy_en; 
      endmethod


      // selects 1 of 16 destination rdy lines.  dest_rdy indicates that 
      // the destination has room for data (not full).
            
      method Action m_dest_rdy(Bit#(16) dest_rdy);
            m_dest_rdy_r <= unpack(dest_rdy[dest_sel]) || !dest_rdy_en; 
      endmethod

      
      method Bit#(16) src_ack();
      
         Bool ack = m_src_rdy_r && burst_cnt==0 && m_state==state_transfer;
         
         Bit#(16) ack_vector;
         ack_vector = 0;

         for (Integer i=0;i<16;i=i+1) begin
            ack_vector[i] = pack(src_sel == fromInteger(i) && ack);
         end
      
         return ack_vector; 
      endmethod

      method Bit#(16) dest_ack();
         Bit#(16) ack_vector;
         ack_vector = 0;

         for (Integer i=0;i<16;i=i+1) begin
            ack_vector[i] = pack(dest_sel== fromInteger(i) && m_state==state_transfer);
         end
      
         return ack_vector;  
      endmethod

   // End Flow Control Methods  
   // -----------------------------------------------------------------
   
endmodule
