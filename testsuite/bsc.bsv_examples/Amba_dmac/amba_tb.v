// date; time iverilog -y $BLUESPECDIR/Verilog -o amba_tb  mkDMAC.v  amba_tb.v; amba_tb
//
//  0.040u 0.000s 0:00.03 133.3%   0+0k 0+0io 1635pf+0w
//  Start of Test
//  Reset complete
//  write and read slave
//                   164: hrdata= 00000000
//
//                   220: hrdata= 22225678
//
//                   236: hrdata= 11115678
//
//                   252: hrdata= 22225678
//
//  End of Test

module amba_tb();
   integer        test_in_progress;
   integer        i;
   integer        loopi;
   integer        cnt;

   integer        transfer_cnt;

   reg [8*20:1]   str;

// dut signals
   reg  CLK;
   reg  RST_N;
   reg  s_hsel;
   reg  [31 : 0] s_haddr;
   reg  s_hwrite;
   reg  [31 : 0] s_hwdata;
   wire [31 : 0] m_hrdata;
   reg  s_hready_in;
   // reg  EN_s_write_data;
   reg  m_hgrant;
   // reg  m_hready;
   wire [15 : 0] m_src_rdy;
   wire [15 : 0] m_dest_rdy;
   // wire RDY_s_hready_in;
   // wire RDY_s_write_data;
   wire s_hready_out;
   wire RDY_s_hready_out;
   wire [31 : 0] s_hrdata;
   wire RDY_s_hrdata;
   wire [1 : 0] s_hresp;
   wire RDY_s_hresp;
   wire m_hbusreq;
   wire RDY_m_hready;
   wire [31 : 0] m_hwdata;
   wire RDY_m_hwdata;
   wire [31 : 0] m_haddr;
   wire RDY_m_haddr;
   wire m_hwrite;
   wire RDY_m_hwrite;
   wire RDY_m_src_rdy;
   wire RDY_m_dest_rdy;
   wire [15 : 0] src_ack;
   wire RDY_src_ack;
   wire [15 : 0] dest_ack;
   wire RDY_dest_ack;
   wire interrupt;

   reg  EN_m_hresp;
   wire RDY_m_hresp;
   
   reg  [3:0] src_sel;
   reg  [3:0] dest_sel;

   //reg  [1:0] m_hresp_code;
   wire [1:0] m_htrans;


   wire  [31:0] haddr;   

   wire  [31:0] hrdata;
   wire  [31:0] hrdata0;
   wire  [31:0] hrdata1;
   wire  [31:0] hrdata2;
   wire  [31:0] hrdata3;
   wire  [31:0] hrdatadefault;
   
   wire         hready;

   wire         m_hready;
   wire   [1:0] m_hresp;
   wire   [1:0] hresp;
   wire   [1:0] hresp0;
   wire   [1:0] hresp1;
   wire   [1:0] hresp2;
   wire   [1:0] hresp3;
   wire   [1:0] hrespdefault;
   wire   [1:0] htrans;
   wire         hwrite;
   wire  [31:0] hwdata;
   
   assign haddr    = m_haddr;
   assign m_hrdata = hrdata;
   assign m_hready = hready;
   assign m_hresp  = hresp;
   assign hwrite   = m_hwrite;
   assign htrans   = m_htrans;
   assign hwdata   = m_hwdata;

   reg         rx_write2;
   reg  [31:0] rx_d2;
   reg         tx_read2;
   wire [31:0] tx_d2;

   reg         rx_write3;
   reg  [31:0] rx_d3;
   reg         tx_read3;
   wire [31:0] tx_d3;
   
   reg  [31:0] expect_value;

   integer rx2_speed;
   integer tx2_speed;
   integer rx3_speed;
   integer tx3_speed;

   integer offset;

   // --------------------------------

   task write_to_slave;
      input  [31:0] addr;
      input  [31:0] data;
  	   begin
//         $display("%t: write addr=0x%x data=0x%x",$time,addr,data);
         s_hready_in<= 1;
         s_hsel  <= 1;
         s_haddr <= addr;
         s_hwrite <= 1;
         @(posedge CLK);
         s_hwdata <= data;      
         s_hsel   <= 0;
         s_haddr  <= 0;
         s_hwrite <= 0;
         @(posedge CLK);
  	   end
   endtask

   task read_from_slave;
      input  [31:0] addr;
      begin
         s_hready_in<= 1;
         s_hsel  <= 1;
         s_haddr <= addr;
         s_hwrite <= 0;
         @(posedge CLK);
         @(posedge CLK);
//         $display("%t: read  addr=0x%x data=0x%x",$time,addr,s_hrdata); 
      end
   endtask


   task fillmem;
      input [31:0]   daddr;         
      input [31:0]   value;
      input [31:0]   transfer_cnt;  
      input [8*20:1] istr;
//      input  [4:0]   dsel;  // assume ram for now
//      input  [9:0]   dstep; // assume 4 for now
      
      begin          
         str = istr;
         $display ("%t: %s", $time,str);
         write_to_slave(9, 32'h1); // fill constant 
         write_to_slave(0, 32'h0000_0000); // +1000*cnt); // src_addr
         write_to_slave(1, daddr); // +2000*cnt); // dest_addr      
         write_to_slave(3, 32'h0000_000f); // interrupt Enable/Mask 1=enabled 0=masked
         write_to_slave(4, 32'h0); // interrupt clear
         write_to_slave(5, 32'h0); // interrupt status
   //      write_to_slave(7, {14'h0,d_sel[4:0],2'b0,10'h4}); // dest config {[31:16],sel[15:12],[11:10],step[9:0]}
         write_to_slave(7, {14'h0,5'h0,2'b0,10'h4}); // dest config {[31:16],sel[15:12],[11:10],step[9:0]}
          write_to_slave(10, value);
         write_to_slave(2, transfer_cnt); // set transfer_cnt
         read_from_slave(5); 
         @(posedge interrupt);
         @(posedge CLK);
         read_from_slave(5); 
         if (s_hrdata!==32'h1) begin
            $display("int_vector=0x%x, expected=0x%x",s_hrdata,32'h0000_0001);
         end
      end
   endtask


   task mem2mem;
      input  [4:0]     ssel;
      input [31:0]     saddr;
      input  [9:0]     sstep;
      input  [4:0]     dsel;
      input [31:0]     daddr;
      input  [9:0]     dstep;
      input [31:0]     transfer_cnt;
      input [8*20:1]   istr;

      begin

         str = istr;
         $display ("%t: %s", $time,str);
         
         // Initial Source RAM, X out Dest RAM
         for (i=0;i<1024;i=i+1) begin
            case (dsel)
               0: u_ram0.u_ram.mem[i] = 32'hx;
               1: u_ram1.u_ram.mem[i] = 32'hx;
            endcase
            case (ssel)
               0: u_ram0.u_ram.mem[i] = 32'h4321_0000+i;
               1: u_ram1.u_ram.mem[i] = 32'h4321_0000+i;
            endcase            
         end
         
         if (ssel==5'h12)
            write_to_slave(9, 32'h0000_0100);  //
         else begin
            write_to_slave(9, 32'h0000_0000);  // fill increment starting with h1234_0000
         end
         write_to_slave(0, saddr); // +1000*cnt); // src_addr
         write_to_slave(1, daddr); // +2000*cnt); // dest_addr      
         write_to_slave(3, 32'h0000_000f); // interrupt Enable/Mask 1=enabled 0=masked
         write_to_slave(4, 32'h0); // interrupt clear
         write_to_slave(5, 32'h0); // interrupt status
         write_to_slave(6, {15'h0,ssel[4:0],2'b0,sstep});  // src  config {[31:16],sel[15:12],[11:10],step[9:0]}
         write_to_slave(7, {15'h0,dsel[4:0],2'b0,dstep}); // dest config {[31:16],sel[15:12],[11:10],step[9:0]}
         write_to_slave(2, transfer_cnt); // set transfer_cnt
         read_from_slave(5);
         
         // rx_d2 <= 32'ha987_0000;
         @(posedge CLK);
         if (ssel==5'h12) begin
            rx2_speed = 15;
            tx2_speed = 15;
         end

         @(posedge interrupt);
         @(posedge CLK);
         rx2_speed = 0;
         tx2_speed = 0;
          
         // Verify Interrupt vector indicates Transfer Done
         read_from_slave(5); 
         if (s_hrdata!==32'h1) begin
            $display("int_vector=0x%x, expected=0x%x",s_hrdata,32'h0000_0001);
         end

         
         expect_value = (ssel<2) ? 32'h4321_0000 : 32'h0000_0000+offset;

         // Verify Written Contents of Destination RAM
         for (i=0;i<transfer_cnt;i=i+1) begin
            case (dsel)
               0: if (u_ram0.u_ram.mem[i]!==expect_value+i) begin
                     $display("ram0[%d]=0x%x, expected=0x%x",i,u_ram0.u_ram.mem[i],expect_value+i);
                  end
               1: if (u_ram1.u_ram.mem[i]!==expect_value+i) begin
                     $display("ram1[%d]=0x%x, expected=0x%x",i,u_ram1.u_ram.mem[i],expect_value+i);
                  end
            endcase 
         end

         //  Verify Unwritten Contents did not change
         for (i=transfer_cnt;i<1024;i=i+1) begin
            case (dsel)
               0: if (u_ram0.u_ram.mem[i]!==32'hx) begin
                     $display("ram0[%d]=0x%x, expected=all_x",i,u_ram0.u_ram.mem[i]);
                  end
               1: if (u_ram1.u_ram.mem[i]!==32'hx) begin
                     $display("ram1[%d]=0x%x, expected=all_x",i,u_ram1.u_ram.mem[i]);
                  end
            endcase 
         end
      end
   endtask


   always  #4 CLK <= !CLK;

   assign m_src_rdy[15:4]  = 12'hfff;
   assign m_src_rdy[1:0]   = 2'h3;
   assign m_dest_rdy[15:4] = 12'hfff;
   assign m_dest_rdy[1:0]  = 2'h3;

   initial begin: fail_safe
      repeat (100) repeat(1000) @(posedge CLK);
      $display("FAIL - SIMULATION TIMED OUT");
      $finish;
   end

   initial begin: rx2
      repeat(10) @(posedge CLK);
      rx_d2 <= 0;
      while (1) begin
         if (rx2_speed==0) begin
            rx_write2 <= 1'b0;
            @(posedge CLK); 
         end
         else begin
            rx_write2 <= 1'b0;
            repeat(rx2_speed)  @(posedge CLK);
            rx_write2 <= 1'b1; @(posedge CLK);
            rx_d2 <= rx_d2+1;
         end
      end
   end
   
   initial begin: tx2
      repeat(10) @(posedge CLK);
      while (1) begin
         tx_read2 <= 1'b0;
         repeat(tx2_speed) @(posedge CLK);
         tx_read2 <= 1'b1; @(posedge CLK);
      end
   end
   
   initial begin: rx3
      repeat(10) @(posedge CLK);
      rx_d3 <= 0;
      while (1) begin
         if (rx3_speed==0)
            @(posedge CLK); 
         else begin
            rx_write3 <= 1'b0;
            repeat(rx3_speed) @(posedge CLK);
            rx_write3 <= 1'b1;
            rx_d3 <= rx_d3+1; @(posedge CLK);
         end
      end
   end
   
   initial begin: tx3
      repeat(10) @(posedge CLK);
      while (1) begin
         tx_read3 <= 1'b0;
         repeat(tx3_speed) @(posedge CLK);
         tx_read3 <= 1'b1; @(posedge CLK);
      end
   end
      

   // -----------------------------------------------
   // Source Slave

   initial begin: main_test

      rx2_speed = 0;
      tx2_speed = 0;
      rx3_speed = 7;
      tx3_speed = 7;


   //    $vcdpluson;   // used in vcs to turn on waves

      $dumpfile("amba_tb.vcd.dump"); // used in cver/iverilog to turn on waves (vcd)
      $dumpvars(0, amba_tb);         // used in cver/iverilog to turn on waves

      test_in_progress <= 1;
//      $display("Start of Test");

 
      transfer_cnt <= 0;

      CLK <= 0;
      m_hgrant <= 1'b1;
        
      src_sel = 0;
      dest_sel = 15;
      // reset for 16 clocks
      RST_N <= 1'b1;
      @(posedge CLK);
      RST_N <= 1'b0;
      repeat(10) @(posedge CLK);
      RST_N <= 1;
      repeat(10) @(posedge CLK);
      $display("%t: Reset complete",$time);

// =======================================================================================
               
      $display ("%t: Fill Memory Bank 0 (Incrementing Pattern)", $time);
      str = "Fill_Incr Bank 0";
      write_to_slave(9, 32'h2);  // fill increment starting with h1234_0000
      write_to_slave(0, 32'h0000_0000); // +1000*cnt); // src_addr
      write_to_slave(1, 32'h0000_0000); // +2000*cnt); // dest_addr      
      write_to_slave(3, 32'h0000_000f); // interrupt Enable/Mask 1=enabled 0=masked
      write_to_slave(4, 32'h0); // interrupt clear
      write_to_slave(5, 32'h0); // interrupt status
      write_to_slave(6, {15'h0,src_sel[3:0],2'b0,10'h4});  // src  config {[31:16],sel[15:12],[11:10],step[9:0]}
      write_to_slave(7, {15'h0,dest_sel[3:0],2'b0,10'h4}); // dest config {[31:16],sel[15:12],[11:10],step[9:0]}
      write_to_slave(10, 32'h1234_0000);
      write_to_slave(2, 512); // set transfer_cnt
      read_from_slave(5); 
      @(posedge interrupt);
      @(posedge CLK);
      read_from_slave(5); 
      if (s_hrdata!==32'h1) begin
         $display("int_vector=0x%x, expected=0x%x",s_hrdata,32'h0000_0001);
      end

      for (i=0;i<512;i=i+1) begin 
          if (u_ram0.u_ram.mem[i]!==32'h1234_0000+i) begin
            $display("ram[%d]=0x%x, expected=0x%x",i,u_ram1.u_ram.mem[i],32'h1234_0000+i);
          end
      end

      for (i=512;i<1024;i=i+1) begin 
          if (u_ram0.u_ram.mem[i]!==32'hxxxx_xxxx) begin
            $display("ram[%d]=0x%x, expected=all_x",i,u_ram1.u_ram.mem[i]);
          end
      end
               
// =======================================================================================
               
      $display ("%t: Fill Memory Bank 1 (Constant Pattern)", $time);
      str = "Fill Bank 1";
      write_to_slave(9, 32'h1); // fill constant DEAD_BEAC
      write_to_slave(0, 32'h0000_0000); // +1000*cnt); // src_addr
      write_to_slave(1, 32'h1000_0000); // +2000*cnt); // dest_addr      
      write_to_slave(3, 32'h0000_000f); // interrupt Enable/Mask 1=enabled 0=masked
      write_to_slave(4, 32'h0); // interrupt clear
      write_to_slave(5, 32'h0); // interrupt status
      write_to_slave(6, {15'h0,src_sel[3:0],2'b0,10'h4});  // src  config {[31:16],sel[15:12],[11:10],step[9:0]}
      write_to_slave(7, {15'h0,dest_sel[3:0],2'b0,10'h4}); // dest config {[31:16],sel[15:12],[11:10],step[9:0]}
      write_to_slave(10, 32'hDEAD_BEAC);
      write_to_slave(2, 512); // set transfer_cnt
      read_from_slave(5); 
      @(posedge interrupt);
      @(posedge CLK);
      read_from_slave(5); 
      if (s_hrdata!==32'h1) begin
         $display("int_vector=0x%x, expected=0x%x",s_hrdata,32'h0000_0001);
      end
      
      
      for (i=0;i<512;i=i+1) begin 
          if (u_ram1.u_ram.mem[i]!==32'hdead_beac) begin
            $display("ram[%d]=0x%x, expected=0x%x",i,u_ram1.u_ram.mem[i],32'hdeadbeac);
          end
      end

      for (i=512;i<1024;i=i+1) begin 
          if (u_ram1.u_ram.mem[i]!==32'hxxxx_xxxx) begin
            $display("ram[%d]=0x%x, expected=all_x",i,u_ram1.u_ram.mem[i]);
          end
      end




// =======================================================================================

      mem2mem(5'h00,32'h0000_0000,4, 5'h1,32'h1000_0000,4, 100, "xfer 100 from 0 to 1"); 
      mem2mem(5'h01,32'h1000_0000,4, 5'h0,32'h0000_0000,4, 200, "xfer 200 from 1 to 0");     
      mem2mem(5'h00,32'h0000_0000,4, 5'h1,32'h1000_0000,4, 100, "xfer 100 from 0 to 1");

      offset = 0;
      mem2mem(5'h12,32'h2000_0000,0, 5'h1,32'h1000_0000,4, 100, "xfer 100 from 2 to 1");

      offset = offset+100;
      mem2mem(5'h12,32'h2000_0000,0, 5'h1,32'h1000_0000,4, 100, "xfer 100 from 2 to 1");
      offset = offset+100;

      for (loopi=1;loopi<10;loopi=loopi+1) begin
         
         mem2mem(5'h00,32'h0000_0000,4, 5'h1,32'h1000_0000,4, loopi*100, "xfer 100 from 0 to 1"); 
         mem2mem(5'h01,32'h1000_0000,4, 5'h0,32'h0000_0000,4, loopi*57, "xfer 200 from 1 to 0");     
         fillmem(32'h2000_0003,loopi%6,1,"change wait-state"); // addr, value, cnt, comment
         mem2mem(5'h12,32'h2000_0000,0, 5'h1,32'h1000_0000,4, 50*loopi, "xfer 100 from 2 to 1");
         offset = offset+50*loopi;
      
      end

      fillmem(32'h1000_0000,32'hDEAD_BEAC,1,"fillmem"); // addr, value, cnt, comment


// =======================================================================================

      $display ("%t: Destination Error Test", $time);
      str = "Error Test";
      write_to_slave(9, 32'h0);  // fill increment starting with h1234_0000
      write_to_slave(0, 32'h1000_0000); // +1000*cnt); // src_addr
      write_to_slave(1, 32'h5000_0000); // +2000*cnt); // dest_addr Bogus addr - should return error   
      write_to_slave(3, 32'h0000_000f); // interrupt Enable/Mask 1=enabled 0=masked
      write_to_slave(4, 32'h0); // interrupt clear
      write_to_slave(5, 32'h0); // interrupt status
      write_to_slave(6, {14'h0,1'b0,4'h2,2'b0,10'h0});  // src  config {[31:17],rdy_en[16],sel[15:12],[11:10],step[9:0]}
      write_to_slave(7, {14'h0,1'b0,4'h1,2'b0,10'h4}); // dest config {[31:17],rdy_en[16],sel[15:12],[11:10],step[9:0]}
      write_to_slave(2, 512); // set transfer_cnt
      read_from_slave(5); 
      @(posedge interrupt);
      @(posedge CLK);
      read_from_slave(5); 
      if (s_hrdata[3]!==1'b1) begin
         $display("int_vector=0x%x, expected=0b100x",s_hrdata);
      end
      write_to_slave(5,0); // clear interrupt
      read_from_slave(5); 
      if (s_hrdata!==32'h0) begin
         $display("int_vector=0x%x, expected=0x%x",s_hrdata,32'h0000_0000);
      end

      $display ("%t: Source Error Test", $time);
      str = "Error Test";
      write_to_slave(9, 32'h0);  // fill increment starting with h1234_0000
      write_to_slave(0, 32'h5000_0000); // +1000*cnt); // src_addr
      write_to_slave(1, 32'h1000_0000); // +2000*cnt); // dest_addr Bogus addr - should return error   
      write_to_slave(3, 32'h0000_000f); // interrupt Enable/Mask 1=enabled 0=masked
      write_to_slave(4, 32'h0); // interrupt clear
      write_to_slave(5, 32'h0); // interrupt status
      write_to_slave(6, {14'h0,1'b0,4'h2,2'b0,10'h0});  // src  config {[31:17],rdy_en[16],sel[15:12],[11:10],step[9:0]}
      write_to_slave(7, {14'h0,1'b0,4'h1,2'b0,10'h4}); // dest config {[31:17],rdy_en[16],sel[15:12],[11:10],step[9:0]}
      write_to_slave(2, 512); // set transfer_cnt
      read_from_slave(5); 
      @(posedge interrupt);
      @(posedge CLK);
      read_from_slave(5); 
      if (s_hrdata[3]!==1'b1) begin
         $display("int_vector=0x%x, expected=0b100x",s_hrdata);
      end
      write_to_slave(5,0); // clear interrupt
      read_from_slave(5); 
      if (s_hrdata!==32'h0) begin
         $display("int_vector=0x%x, expected=0x%x",s_hrdata,32'h0000_0000);
      end
      
     // read_from_slave
 
      test_in_progress <= 0;
   //   $vcdplusoff;
      for (i=0;i<100;i=i+1) @(posedge CLK );
      $display("End of Test");

      $finish(0);

   end // initial block


   // instantiate dut

   // implemented in Bluespec SystemVerilog
   mkDMAC u_dmac(
      .CLK(CLK),
      .RST_N(RST_N),
      .s_hready_in_s_hsel(s_hsel),
      .s_hready_in_s_haddr(s_haddr),
      .s_hready_in_s_hwrite(s_hwrite),
      .s_write_data_s_hwdata(s_hwdata),
      .m_master_hrdata(m_hrdata),
      .m_master_hgrant(m_hgrant),
      .m_master_hresp(m_hresp),
      .m_src_rdy_src_rdy(m_src_rdy),
      .m_dest_rdy_src_rdy(m_dest_rdy),
      .EN_s_hready_in(s_hready_in),
      .EN_s_write_data(1'b1),
      .EN_m_master(m_hready),
      .EN_m_src_rdy(1'b1),
      .EN_m_dest_rdy(1'b1),
      .RDY_s_hready_in(),
      .RDY_s_write_data(),
      .s_hready_out(),  // same as s_hready_out
      .RDY_s_hready_out(),

      .s_hrdata(s_hrdata),
      .RDY_s_hrdata(s_hready_out), 
      .s_hresp(s_hresp),
      .RDY_s_hresp(),
      .RDY_m_master(m_hbusreq),
      .m_hwdata(m_hwdata),
      .RDY_m_hwdata(),
      .m_haddr(m_haddr),
      .RDY_m_haddr(),
      .m_hwrite(m_hwrite),
      .RDY_m_hwrite(),
      .RDY_m_src_rdy(),
      .RDY_m_dest_rdy(),
      .src_ack(src_ack),
      .RDY_src_ack(RDY_src_ack),
      .dest_ack(dest_ack),
      .RDY_dest_ack(RDY_dest_ack),
      .interrupt(interrupt),
      .m_htrans(m_htrans), 
      .RDY_m_htrans(),
      .RDY_interrupt()        
      );


   // Implemented in Verilog
   ahb_bus u_ahb_bus(
      .hclk(CLK),                    // input 
      .hresetn(RST_N),               // input  

      // Master Interface

      .haddr_31_28(haddr[31:28]),    // input   [3:0]
      .hrdata(hrdata),               // output [31:0] 
      .hready(hready),               // output        
      .hresp(hresp),                 // output  [1:0]  

      // Slave Interfaces

      // Slave0 is a Verilog Internal RAM
      .hsel0(hsel0),                 // output
      .hrdata0(hrdata0),             // input  [31:0] 
      .hready0(hready0),             // input         
      .hresp0(hresp0),               // input   [1:0]  

      // Slave1 is a Verilog Internal RAM
      .hsel1(hsel1),                 // output
      .hrdata1(hrdata1),             // input  [31:0] 
      .hready1(hready1),             // input         
      .hresp1(hresp1),               // input   [1:0]  

      // Slave2 is a Bluespec System Verilog Data Source
      .hsel2(hsel2),                 // output
      .hrdata2(hrdata2),             // input  [31:0] 
      .hready2(hready2),             // input         
      .hresp2(hresp2),               // input   [1:0]  

      // Slave3 is a Bluespec Sysem Verilog Data Sink
      .hsel3(hsel3),                 // output
      .hrdata3(hrdata3),             // input  [31:0] 
      .hready3(hready3),             // input         
      .hresp3(hresp3),               // input   [1:0]  

      .hseldefault(hseldefault),     // output
      .hrdatadefault(32'b0),         // input  [31:0] 
      .hreadydefault(hreadydefault), // input         
      .hrespdefault(hrespdefault));  // input   [1:0]  


   // Implemented in Verilog
   ahb_ram u_ram0(
      .hclk(CLK),                    // input         
      .hresetn(RST_N),               // input         
      .hsel(hsel0),                  // input         
      .hready(hready),               // input         
      .hwrite(hwrite),               // input         
      .htrans(htrans),               // input   [1:0] 
      .haddr(haddr),                 // input  [31:0] 
      .hwdata(hwdata),               // input  [31:0] 
      .hreadyout(hready0),           // output        
      .hresp(hresp0),                // output  [1:0] 
      .hrdata(hrdata0));             // output [31:0] 

   // Implemented in Verilog
   ahb_ram u_ram1(
      .hclk(CLK),                    // input         
      .hresetn(RST_N),               // input         
      .hsel(hsel1),                  // input         
      .hready(hready),               // input         
      .hwrite(hwrite),               // input         
      .htrans(htrans),               // input   [1:0] 
      .haddr(haddr),                 // input  [31:0] 
      .hwdata(hwdata),               // input  [31:0] 
      .hreadyout(hready1),           // output        
      .hresp(hresp1),                // output  [1:0] 
      .hrdata(hrdata1));             // output [31:0] 

   // Implemented in Bluespec System Verilog
   mkSlave u_slave2(
      .CLK(CLK),
      .RST_N(RST_N),

	   .rxtx_rx_nef_rx_ack(src_ack[2]),
      .s_hready_in_s_hsel(hsel2),
      .s_hready_in_s_haddr(haddr),
      .s_hready_in_s_hwrite(hwrite),
	   .s_hready_in_s_htrans(htrans),
      .s_write_data_s_hwdata(hwdata),
	   .s_write_data_s_htrans(htrans),

      .EN_s_hready_in(hready),
      .EN_s_write_data(1'b1),
      .RDY_s_hready_in(),
      .RDY_s_write_data(),
      .s_hready_out(),   // same as s_hready_out
      .RDY_s_hready_out(),
      .s_hrdata(hrdata2),
      .RDY_s_hrdata(hready2), 
      .s_hresp(hresp2),
      .RDY_s_hresp(),
	   .EN_rxtx_rx(rx_write2), // phy pushes data to slave
	   .RDY_rxtx_rx(),
	   .rxtx_rx_d(rx_d2),
	   .EN_rxtx_tx(tx_read2),  // phy pulls data from slave
	   .RDY_rxtx_tx(),
	   .rxtx_tx_d(tx_d2),
	   .RDY_rxtx_tx_d(),
	   .rxtx_rx_nef(m_src_rdy[2]),       
	   .RDY_rxtx_rx_nef(),     
	   .rxtx_tx_nff(m_dest_rdy[2]),         
	   .RDY_rxtx_tx_nff());    

          
   // Implemented in Bluespec System Verilog
   mkSlave u_slave3(
      .CLK(CLK),
      .RST_N(RST_N),
	   .rxtx_rx_nef_rx_ack(src_ack[3]),
      .s_hready_in_s_hsel(hsel3),
      .s_hready_in_s_haddr(haddr),
      .s_hready_in_s_hwrite(hwrite),
	   .s_hready_in_s_htrans(htrans),
      .s_write_data_s_hwdata(hwdata),
	   .s_write_data_s_htrans(htrans),
      .EN_s_hready_in(hready),
      .EN_s_write_data(1'b1),
      .RDY_s_hready_in(),
      .RDY_s_write_data(),
      .s_hready_out(),      // same as s_hready_out
      .RDY_s_hready_out(),
      .s_hrdata(hrdata3),
      .RDY_s_hrdata(hready3), 
      .s_hresp(hresp3),
      .RDY_s_hresp(),
	   .EN_rxtx_rx(rx_write3), // phy pushes data to slave
	   .RDY_rxtx_rx(),
	   .rxtx_rx_d(rx_d3),
	   .EN_rxtx_tx(tx_read3),  // phy pulls data from slave
	   .RDY_rxtx_tx(),
	   .rxtx_tx_d(tx_d3),
	   .RDY_rxtx_tx_d(),
	   .rxtx_rx_nef(m_src_rdy[3]),       
	   .RDY_rxtx_rx_nef(),     
	   .rxtx_tx_nff(m_dest_rdy[3]),         
	   .RDY_rxtx_tx_nff());    

   // Implemented in Verilog
   ahb_default u_ahb_default (
      .hclk(CLK),                    // input 
      .hresetn(RST_N),               // input  
      .hready(hready),               // input
      .hsel(hseldefault),            // input
      .htrans(htrans),               // input [1:0]
      .hreadyout(hreadydefault),     // output
      .hresp(hrespdefault));         // output [1:0]
      

endmodule
