// Accellera Standard V2.8.1 Open Verification Library (OVL).
// Accellera Copyright (c) 2005-2014. All rights reserved.


  bit error_event, error_event_xz;

`ifdef OVL_ASSERT_ON

  always @(posedge ren_clk or posedge wen_clk)
  begin
    error_event = 0;
    error_event_xz = 0;
  end

`endif // OVL_ASSERT_ON

`ifdef OVL_REVISIT // Tied low in V2.3 (in top-level file)
  `ifdef OVL_ASSERT_ON
    assign fire[0] = error_event;
    assign fire[1] = error_event_xz;
  `else
    assign fire[0] = 1'b0;
    assign fire[1] = 1'b0;
  `endif // OVL_ASSERT_ON

  `ifdef OVL_COVER_ON
    assign fire[2] = 1'b0;
  `else
    assign fire[2] = 1'b0;
  `endif // OVL_COVER_ON
`endif // OVL_REVISIT

`ifdef OVL_SHARED_CODE

  wire                    waddr_check;
  wire                    raddr_check;
  wire                    wen_ok;
  wire                    ren_ok;

  wire  [addr_width-1:0]  temp_waddr;
  wire  [addr_width-1:0]  temp_raddr;

  reg  [(mem_size-1):0] sva_v_mem_async_addr_init    = {mem_size{1'b0}};
  reg  [(mem_size-1):0] sva_v_mem_async_write1_flags = {mem_size{1'b0}};
  reg  [(mem_size-1):0] sva_v_mem_async_read1_flags  = {mem_size{1'b0}};

  assign waddr_check = ( ( start_addr <= waddr) &&
                       ( waddr <= end_addr));

  assign raddr_check = ( ( start_addr <= raddr) &&
                       ( raddr <= end_addr));

  assign wen_ok = waddr_check;

  assign ren_ok = raddr_check;

  assign temp_waddr = waddr_check ? waddr : start_addr;
  assign temp_raddr = raddr_check ? raddr : start_addr;

  // Flag the memory address as having been written

  always @( posedge ren_clk) begin
    if (`OVL_RESET_SIGNAL != 1'b1)
      sva_v_mem_async_read1_flags  <= {mem_size{1'b0}};
    else begin
      // Toggle the read bit, if needed
      sva_v_mem_async_read1_flags[temp_raddr] <=
        ren_ok ? (
          (sva_v_mem_async_read1_flags[temp_raddr] ==
           sva_v_mem_async_write1_flags[temp_raddr]) ?
             // Already read once before (or not initialized)
             sva_v_mem_async_read1_flags[temp_raddr] :
             // Toggle the read bit if not read
             ~sva_v_mem_async_read1_flags[temp_raddr] ) :
          sva_v_mem_async_read1_flags[temp_raddr];
    end
  end

  // Adding reset block; Ref Mantis Issue # 2772
  always @( posedge wen_clk) begin
    if (`OVL_RESET_SIGNAL != 1'b1) begin
      sva_v_mem_async_addr_init <= {mem_size{1'b0}};
      sva_v_mem_async_write1_flags <= {mem_size{1'b0}};
    end
    else begin
      sva_v_mem_async_addr_init[temp_waddr]  <=
         wen_ok ? 1'b1 :
          sva_v_mem_async_addr_init[temp_waddr];

      // Toggle the write bit if needed
      sva_v_mem_async_write1_flags[temp_waddr] <=
        wen_ok ? (
          (sva_v_mem_async_write1_flags[temp_waddr] ==
           sva_v_mem_async_read1_flags[temp_waddr]) ?
           // Read at least once, toggle
           ~sva_v_mem_async_write1_flags[temp_waddr] :
           // Don't toggle, previous data not read
              sva_v_mem_async_write1_flags[temp_waddr] ) :
            sva_v_mem_async_write1_flags[temp_waddr];
    end
  end

`endif // OVL_SHARED_CODE

`ifdef OVL_ASSERT_ON

  // check fire signals declaration

  // for value_check

  // We need conditional generation of the mem_async_mirror var,
  // until then,  make size minimal if no value_checks

  reg  [(data_width-1)  : 0] sva_v_mem_async_mirror [(mem_size-1) : 0] = '{mem_size{0}};

  wire [(data_width-1)  : 0] sva_w_data;

  assign sva_w_data = sva_v_mem_async_mirror[temp_raddr];

  // Write data to memory with posedge wen

  always @( posedge wen_clk) begin
    if (`OVL_RESET_SIGNAL != 1'b0) begin
      sva_v_mem_async_mirror[temp_waddr] <=
        wen_ok ? wdata :
          sva_v_mem_async_mirror[temp_waddr];
    end
  end

  property OVL_MEMORY_ASYNC_VALUE_CHK_P;
    @( posedge ren_clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
       (ren_ok && sva_v_mem_async_addr_init[temp_raddr]) |->
                                           (sva_w_data == rdata);
  endproperty

  property OVL_MEMORY_ASYNC_INIT_CHK_P;
    @( posedge ren_clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
       ren_ok |->
         (sva_v_mem_async_addr_init[temp_raddr]);
  endproperty

  property OVL_MEMORY_ASYNC_WADDR_CHK_P;
    @( posedge wen_clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
      waddr_check;
  endproperty

  property OVL_MEMORY_ASYNC_RADDR_CHK_P;
    @( posedge ren_clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
      raddr_check;
  endproperty

  property OVL_MEMORY_ASYNC_WRITE1_CHK_P;
    @(posedge wen_clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
      wen_ok |->
        (sva_v_mem_async_addr_init[temp_waddr] == 0) ||
        (sva_v_mem_async_read1_flags[temp_waddr] ==
         sva_v_mem_async_write1_flags[temp_waddr]);
  endproperty

  property OVL_MEMORY_ASYNC_READ1_CHK_P;
    @(posedge ren_clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
      (ren_ok && sva_v_mem_async_addr_init[temp_raddr]) |->
        (sva_v_mem_async_read1_flags[temp_raddr] !=
         sva_v_mem_async_write1_flags[temp_raddr]);
  endproperty

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else

    property OVL_MEMORY_ASYNC_XZ_ON_START_ADDR_REN_P;
    @(posedge ren_clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    (!($isunknown(start_addr)));
    endproperty

    property OVL_MEMORY_ASYNC_XZ_ON_END_ADDR_REN_P;
    @(posedge ren_clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    (!($isunknown(end_addr)));
    endproperty

    property OVL_MEMORY_ASYNC_XZ_ON_START_ADDR_WEN_P;
    @(posedge wen_clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    (!($isunknown(start_addr)));
    endproperty

    property OVL_MEMORY_ASYNC_XZ_ON_END_ADDR_WEN_P;
    @(posedge wen_clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    (!($isunknown(end_addr)));
    endproperty

    property OVL_MEMORY_ASYNC_XZ_ON_RADDR_P;
    @(posedge ren_clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    (!($isunknown(raddr)));
    endproperty

    property OVL_MEMORY_ASYNC_XZ_ON_RDATA_P;
    @(posedge ren_clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    (!($isunknown(rdata)));
    endproperty

    property OVL_MEMORY_ASYNC_XZ_ON_WADDR_P;
    @(posedge wen_clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    (!($isunknown(waddr)));
    endproperty

    property OVL_MEMORY_ASYNC_XZ_ON_WDATA_P;
    @(posedge wen_clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    (!($isunknown(wdata)));
    endproperty

  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

  generate
    case (property_type)
      `OVL_ASSERT_2STATE,
      `OVL_ASSERT: begin : ovl_assert

        if(value_check) begin : value_check
          A_OVL_MEMORY_ASYNC_VALUE_CHK_P:
          assert property (OVL_MEMORY_ASYNC_VALUE_CHK_P)
          else begin
            ovl_error_t(`OVL_FIRE_2STATE,"data read is not same as data written");
            error_event = 1;
          end
        end : value_check

        if(init_check) begin : init_check
          A_OVL_MEMORY_ASYNC_INIT_CHK_P:
          assert property (OVL_MEMORY_ASYNC_INIT_CHK_P)
          else begin
            ovl_error_t(`OVL_FIRE_2STATE,"uninitialized location is read");
            error_event = 1;
          end
        end : init_check

        if(addr_check) begin : addr_check
          A_OVL_MEMORY_ASYNC_WADDR_CHK_P:
          assert property (OVL_MEMORY_ASYNC_WADDR_CHK_P)
          else begin
            ovl_error_t(`OVL_FIRE_2STATE,"write address is not within range of start and end address");
            error_event = 1;
          end

          A_OVL_MEMORY_ASYNC_RADDR_CHK_P:
          assert property (OVL_MEMORY_ASYNC_RADDR_CHK_P)
          else begin
            ovl_error_t(`OVL_FIRE_2STATE,"read address is not within range of start and end address");
            error_event = 1;
          end
        end : addr_check

        if(one_write_check) begin : write1_check
          A_OVL_MEMORY_ASYNC_WRITE1_CHK_P:
          assert property (OVL_MEMORY_ASYNC_WRITE1_CHK_P)
          else begin
            ovl_error_t(`OVL_FIRE_2STATE,"data is not read before it is overwritten");
            error_event = 1;
          end
        end : write1_check

        if(one_read_check) begin : read1_check
          A_OVL_MEMORY_ASYNC_READ1_CHK_P:
          assert property (OVL_MEMORY_ASYNC_READ1_CHK_P)
          else begin
            ovl_error_t(`OVL_FIRE_2STATE,"there is more than 1 read between 2 successive writes");
            error_event = 1;
          end
        end : read1_check

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else

        A_OVL_MEMORY_ASYNC_XZ_ON_START_ADDR_REN_P:
        assert property (OVL_MEMORY_ASYNC_XZ_ON_START_ADDR_REN_P)
        else begin
          ovl_error_t(`OVL_FIRE_XCHECK,"start address contains X or Z");
          error_event_xz = 1;
        end

        A_OVL_MEMORY_ASYNC_XZ_ON_END_ADDR_REN_P:
        assert property (OVL_MEMORY_ASYNC_XZ_ON_END_ADDR_REN_P)
        else begin
          ovl_error_t(`OVL_FIRE_XCHECK,"end address contains X or Z");
          error_event_xz = 1;
        end

        A_OVL_MEMORY_ASYNC_XZ_ON_START_ADDR_WEN_P:
        assert property (OVL_MEMORY_ASYNC_XZ_ON_START_ADDR_WEN_P)
        else begin
          ovl_error_t(`OVL_FIRE_XCHECK,"start address contains X or Z");
          error_event_xz = 1;
        end

        A_OVL_MEMORY_ASYNC_XZ_ON_END_ADDR_WEN_P:
        assert property (OVL_MEMORY_ASYNC_XZ_ON_END_ADDR_WEN_P)
        else begin
          ovl_error_t(`OVL_FIRE_XCHECK,"end address contains X or Z");
          error_event_xz = 1;
        end

        A_OVL_MEMORY_ASYNC_XZ_ON_RADDR_P:
        assert property (OVL_MEMORY_ASYNC_XZ_ON_RADDR_P)
        else begin
          ovl_error_t(`OVL_FIRE_XCHECK,"read address contains X or Z");
          error_event_xz = 1;
        end

        A_OVL_MEMORY_ASYNC_XZ_ON_RDATA_P:
        assert property (OVL_MEMORY_ASYNC_XZ_ON_RDATA_P)
        else begin
          ovl_error_t(`OVL_FIRE_XCHECK,"read data contains X or Z");
          error_event_xz = 1;
        end

        A_OVL_MEMORY_ASYNC_XZ_ON_WADDR_P:
        assert property (OVL_MEMORY_ASYNC_XZ_ON_WADDR_P)
        else begin
          ovl_error_t(`OVL_FIRE_XCHECK,"write address contains X or Z");
          error_event_xz = 1;
        end

        A_OVL_MEMORY_ASYNC_XZ_ON_WDATA_P:
        assert property (OVL_MEMORY_ASYNC_XZ_ON_WDATA_P)
        else begin
          ovl_error_t(`OVL_FIRE_XCHECK,"write data contains X or Z");
          error_event_xz = 1;
        end

  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

      end

      `OVL_ASSUME_2STATE,
      `OVL_ASSUME: begin : ovl_assume

        if(value_check) begin : value_check
          M_OVL_MEMORY_ASYNC_VALUE_CHK_P:
          assume property (OVL_MEMORY_ASYNC_VALUE_CHK_P);
        end : value_check

        if(init_check) begin : init_check
          M_OVL_MEMORY_ASYNC_INIT_CHK_P:
          assume property (OVL_MEMORY_ASYNC_INIT_CHK_P);
        end : init_check

        if(addr_check) begin : addr_check
          M_OVL_MEMORY_ASYNC_WADDR_CHK_P:
          assume property (OVL_MEMORY_ASYNC_WADDR_CHK_P);

          M_OVL_MEMORY_ASYNC_RADDR_CHK_P:
          assume property (OVL_MEMORY_ASYNC_RADDR_CHK_P);
        end : addr_check

        if(one_write_check) begin : write1_check
          M_OVL_MEMORY_ASYNC_WRITE1_CHK_P:
          assume property (OVL_MEMORY_ASYNC_WRITE1_CHK_P);
        end : write1_check

        if(one_read_check) begin : read1_check
          M_OVL_MEMORY_ASYNC_READ1_CHK_P:
          assume property (OVL_MEMORY_ASYNC_READ1_CHK_P);
        end : read1_check

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else

        M_OVL_MEMORY_ASYNC_XZ_ON_START_ADDR_REN_P:
        assume property (OVL_MEMORY_ASYNC_XZ_ON_START_ADDR_REN_P);

        M_OVL_MEMORY_ASYNC_XZ_ON_END_ADDR_REN_P:
        assume property (OVL_MEMORY_ASYNC_XZ_ON_END_ADDR_REN_P);

        M_OVL_MEMORY_ASYNC_XZ_ON_START_ADDR_WEN_P:
        assume property (OVL_MEMORY_ASYNC_XZ_ON_START_ADDR_WEN_P);

        M_OVL_MEMORY_ASYNC_XZ_ON_END_ADDR_WEN_P:
        assume property (OVL_MEMORY_ASYNC_XZ_ON_END_ADDR_WEN_P);

        M_OVL_MEMORY_ASYNC_XZ_ON_RADDR_P:
        assume property (OVL_MEMORY_ASYNC_XZ_ON_RADDR_P);

        M_OVL_MEMORY_ASYNC_XZ_ON_RDATA_P:
        assume property (OVL_MEMORY_ASYNC_XZ_ON_RDATA_P);

        M_OVL_MEMORY_ASYNC_XZ_ON_WADDR_P:
        assume property (OVL_MEMORY_ASYNC_XZ_ON_WADDR_P);

        M_OVL_MEMORY_ASYNC_XZ_ON_WDATA_P:
        assume property (OVL_MEMORY_ASYNC_XZ_ON_WDATA_P);

  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

      end

      `OVL_IGNORE : begin : ovl_ignore
        // do nothing;
      end
      default     : initial ovl_error_t(`OVL_FIRE_2STATE,"");
    endcase
  endgenerate

`endif // OVL_ASSERT_ON


`ifdef OVL_COVER_ON

  reg [(mem_size-1):0] sva_v_mem_read_once = 0;

  always @ ( posedge ren_clk) begin
    if (`OVL_RESET_SIGNAL != 1'b0) begin
      sva_v_mem_read_once[temp_raddr] <=
        ren_ok || sva_v_mem_read_once[temp_raddr];
    end
  end

`ifdef OVL_COVERGROUP_ON

  covergroup read_addr_cg @(posedge ren_clk);
    coverpoint raddr
      iff(`OVL_RESET_SIGNAL != 1'b0);
    option.per_instance = 1;
    option.at_least = 1;
    option.name = "observed_read_addr";
    option.comment = "Bin index is the read addresses which have been read at least once";
    option.auto_bin_max = ( ((1<<addr_width)-1) > `OVL_AUTO_BIN_MAX ) ?
                          `OVL_AUTO_BIN_MAX : ((1<<addr_width)-1);
  endgroup :read_addr_cg

  covergroup write_addr_cg @(posedge wen_clk);
    coverpoint waddr
      iff (`OVL_RESET_SIGNAL != 1'b0);
    option.per_instance = 1;
    option.at_least = 1;
    option.name = "observed_write_addr";
    option.comment = "Bin index is the write addresses which have been written at least once";
    option.auto_bin_max = ( ((1<<addr_width)-1) > `OVL_AUTO_BIN_MAX ) ?
                          `OVL_AUTO_BIN_MAX : ((1<<addr_width)-1);
  endgroup :write_addr_cg

`endif  // `ifdef OVL_COVERGROUP_ON

  generate

    if (coverage_level != `OVL_COVER_NONE) begin : ovl_cover

      if (OVL_COVER_SANITY_ON) begin : ovl_cover_sanity

        cover_number_of_reads :
           cover property(
              @( posedge ren_clk)
                 (`OVL_RESET_SIGNAL != 1'b0))
           ovl_cover_t("Read operation is performed");

        cover_number_of_writes :
           cover property(
              @( posedge wen_clk)
                (`OVL_RESET_SIGNAL != 1'b0))
           ovl_cover_t("Write operation is performed");

      end : ovl_cover_sanity

      if (OVL_COVER_BASIC_ON) begin : ovl_cover_basic

         cover_write_followed_by_read :
           cover property(
              @( posedge ren_clk) (`OVL_RESET_SIGNAL != 1'b0) &&
                ren_ok &&(sva_v_mem_async_read1_flags[temp_raddr] !=
              sva_v_mem_async_write1_flags[temp_raddr]))
           ovl_cover_t("Write followed by a read operation to the same address is performed");

      end : ovl_cover_basic

      if (OVL_COVER_STATISTIC_ON) begin : ovl_cover_statistic

`ifdef OVL_COVERGROUP_ON

        read_addr_cg cover_read_addr_cover = new();

        write_addr_cg cover_write_addr_cover = new();

`endif

        cover_two_or_more_writes_without_intervening_read :
          cover property(
            @ ( posedge wen_clk) ((`OVL_RESET_SIGNAL != 1'b0) &&
              wen_ok && (sva_v_mem_async_read1_flags[temp_waddr] !=
                sva_v_mem_async_write1_flags[temp_waddr])))
           ovl_cover_t("Two or more writes without intervening read is covered");

        cover_two_or_more_reads_without_intervening_write :
          cover property(
            @ ( posedge ren_clk) ((`OVL_RESET_SIGNAL != 1'b0) &&
              ren_ok && sva_v_mem_read_once[temp_raddr] &&
                (sva_v_mem_async_read1_flags[temp_raddr] ==
                  sva_v_mem_async_write1_flags[temp_raddr])))
           ovl_cover_t("Two or more reads without intervening write is covered");

      end : ovl_cover_statistic

      if (OVL_COVER_CORNER_ON) begin : ovl_cover_corner

        cover_read_to_start_addr :
           cover property(
              @(posedge ren_clk) (`OVL_RESET_SIGNAL != 1'b0) &&
                 ren_ok && ( raddr==start_addr))
           ovl_cover_t("Read operation is performed at start address");

        cover_write_to_start_addr :
           cover property(
              @(posedge wen_clk) (`OVL_RESET_SIGNAL != 1'b0) &&
                 wen_ok && ( waddr==start_addr))
           ovl_cover_t("write operation is performed at start address");

        cover_read_to_end_addr :
           cover property(
              @(posedge ren_clk) (`OVL_RESET_SIGNAL != 1'b0) &&
                 ren_ok && ( raddr==end_addr))
           ovl_cover_t("Read operation is performed at end address");

        cover_write_to_end_addr :
           cover property(
              @(posedge wen_clk) (`OVL_RESET_SIGNAL != 1'b0) &&
                 wen_ok && ( waddr==end_addr))
           ovl_cover_t("Write operation is performed at end address");

        cover_write_followed_by_read_to_start_addr :
           cover property(
              @(posedge ren_clk) (`OVL_RESET_SIGNAL != 1'b0) &&
                 ren_ok && (sva_v_mem_async_read1_flags[start_addr] !=
                    sva_v_mem_async_write1_flags[start_addr]))
           ovl_cover_t("Write followed by read operation is performed at start address");

        cover_write_followed_by_read_to_end_addr :
           cover property(
              @(posedge ren_clk) (`OVL_RESET_SIGNAL != 1'b0) &&
                 ren_ok && (sva_v_mem_async_read1_flags[end_addr] !=
                    sva_v_mem_async_write1_flags[end_addr]))
           ovl_cover_t("Write followed by read operation is performed at end address");

      end : ovl_cover_corner

    end : ovl_cover

  endgenerate

`endif // OVL_COVER_ON
