// Accellera Standard V2.8.1 Open Verification Library (OVL).
// Accellera Copyright (c) 2005-2014. All rights reserved.


  bit error_event, error_event_xz;
  bit preload_reg;

`ifdef OVL_ASSERT_ON

  always @(posedge clk)
  begin
    error_event = 0;
    error_event_xz = 0;
  end

`endif // OVL_ASSERT_ON


`ifdef OVL_REVISIT // Tied low in V2.4 (in top-level file)
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

  localparam             ptr_width              = log2(depth);

  wire                   sva_v_deferred_deq;
  wire                   sva_v_deferred_enq;

  reg   [ptr_width-1:0]  sva_v_head_ptr         = 'h0;
  reg   [ptr_width-1:0]  sva_v_tail_ptr         = 'h0;
  reg   [ptr_width  :0]  sva_v_q_size           = 'b0;
  reg                    sva_v_hi_water_failed  = 1'b0;
  reg   [ptr_width  :0]  past_sva_v_q_size      = 'b0;

always @(posedge clk)
    past_sva_v_q_size <= sva_v_q_size;

  always @ (posedge clk) begin
    if(`OVL_RESET_SIGNAL != 1'b1) begin
      sva_v_q_size <= preload_count;
    end
    else begin
      if( sva_v_deferred_deq &&
          sva_v_deferred_enq) begin
        if( sva_v_q_size == 0) begin
          sva_v_q_size <= (pass_thru  ? 0 : sva_v_q_size + 1);
        end
        else if( sva_v_q_size == depth) begin
          sva_v_q_size <= (registered  ? depth : sva_v_q_size - 1);
        end
        else begin
          sva_v_q_size <= sva_v_q_size;
        end
      end
      else begin
        if( sva_v_deferred_enq &&
            ( sva_v_q_size < depth)) begin
          sva_v_q_size <= sva_v_q_size + 1;
        end
        else begin
          if( sva_v_deferred_deq &&
              ( sva_v_q_size > 0)) begin
            sva_v_q_size <= sva_v_q_size - 1;
          end
          else begin
            sva_v_q_size <= sva_v_q_size;
          end
        end
      end
    end
  end

  wire fifo_full, fifo_empty;

  assign fifo_empty = (sva_v_q_size == 0);
  assign fifo_full  = (sva_v_q_size == depth);

  always @ (posedge clk) begin
    if(`OVL_RESET_SIGNAL != 1'b1) begin
      sva_v_hi_water_failed <= 0;
    end
    else begin
      sva_v_hi_water_failed <= (high_water_mark == 0) ? 0 :
                               (sva_v_q_size >= high_water_mark);
    end
  end

  generate
    if( deq_latency > 1) begin : deq_lat_g_1
      reg   [deq_latency-1 : 0]  sva_v_deferred_deq_sr = {deq_latency{1'b0}};
      assign sva_v_deferred_deq = sva_v_deferred_deq_sr[deq_latency-1];
      always @(posedge clk) begin
        sva_v_deferred_deq_sr <=
          (`OVL_RESET_SIGNAL != 1'b1) ? 0 :
            { sva_v_deferred_deq_sr[deq_latency-2 : 0],deq};
      end
    end : deq_lat_g_1

    if( deq_latency == 1) begin : deq_lat_e_1
      reg   sva_v_deferred_deq_sr = 1'b0;
      assign sva_v_deferred_deq = sva_v_deferred_deq_sr;
      always @ (posedge clk) begin
        sva_v_deferred_deq_sr <=
          (`OVL_RESET_SIGNAL != 1'b1) ? 0 :
            deq;
      end
    end : deq_lat_e_1

    if( deq_latency == 0) begin : deq_lat_e_0
      assign sva_v_deferred_deq = deq;
    end : deq_lat_e_0

`ifdef OVL_SYNTHESIS
`else
    if( deq_latency < 0) begin : deq_lat_l_0
      initial $display("illegal deq_latency parameter value");
    end : deq_lat_l_0
`endif

    if( enq_latency > 1) begin : enq_lat_g_1
      reg   [enq_latency-1 : 0]  sva_v_deferred_enq_sr = {enq_latency{1'b0}};
      assign sva_v_deferred_enq = sva_v_deferred_enq_sr[enq_latency-1];
      always @(posedge clk) begin
        sva_v_deferred_enq_sr <=
          (`OVL_RESET_SIGNAL != 1'b1) ? 0 :
            { sva_v_deferred_enq_sr[enq_latency-2 : 0],enq};
      end
    end : enq_lat_g_1

    if( enq_latency == 1) begin : enq_lat_e_1
      reg   sva_v_deferred_enq_sr = 1'b0;
      assign sva_v_deferred_enq = sva_v_deferred_enq_sr;
      always @ (posedge clk) begin
        sva_v_deferred_enq_sr <=
          (`OVL_RESET_SIGNAL != 1'b1) ? 0 :
            enq;
      end
    end : enq_lat_e_1

    if( enq_latency == 0) begin : enq_lat_e_0
      assign sva_v_deferred_enq = enq;
    end : enq_lat_e_0

`ifdef OVL_SYNTHESIS
`else
    if( enq_latency < 0) begin : enq_lat_l_0
      initial $display("illegal enq_latency parameter value");
    end : enq_lat_l_0

    if(preload_count > depth) begin : preload_count_g_depth
      initial $display("illegal preload_count parameter value");
    end : preload_count_g_depth
`endif

  endgenerate

    always @ (posedge clk) begin

      // Updated head ptr deq
      if(`OVL_RESET_SIGNAL != 1'b1) begin
        sva_v_head_ptr <= 0;
      end
      else begin
        if( sva_v_deferred_deq &&
           ( sva_v_q_size > 0)) begin
            sva_v_head_ptr <=
              ( sva_v_head_ptr == depth-1) ? 0 :
              ( sva_v_head_ptr + 1);
        end
      end

      // Updated tail ptr deq
      if(`OVL_RESET_SIGNAL != 1'b1) begin
          sva_v_tail_ptr <= ((preload_count == depth) ? 0 : preload_count);
      end
      else begin
        if( sva_v_deferred_deq &&
            sva_v_deferred_enq &&
            sva_v_q_size == 0 && pass_thru) begin
            sva_v_tail_ptr <= sva_v_tail_ptr;
        end
        else if(sva_v_deferred_deq &&
                sva_v_deferred_enq &&
                sva_v_q_size == depth) begin
          sva_v_tail_ptr <= registered ?
           ((sva_v_tail_ptr == depth-1) ? 0 : (sva_v_tail_ptr + 1))
                                       : sva_v_tail_ptr;
        end
        else begin
          if( sva_v_deferred_enq &&
              ( ( sva_v_q_size < depth) ||
              sva_v_deferred_deq)) begin
              sva_v_tail_ptr <=
                ( sva_v_tail_ptr == depth-1) ? 0 :
                ( sva_v_tail_ptr + 1);
          end
          else begin
            sva_v_tail_ptr <= sva_v_tail_ptr;
          end
        end
      end // else: !if(`OVL_RESET_SIGNAL != 1'b1)
    end // always @ (posedge clk)

`endif // OVL_SHARED_CODE

`ifdef OVL_ASSERT_ON



  reg [(width-1):0] sva_v_q [(depth-1):0];

//Initialize queue so that all simulators can handle, ref Mantis#3119
  integer i;
  initial begin
   for (i=0;i<depth;i=i+1) begin
    sva_v_q[i] = {width{1'b0}};
   end
  end

  wire [(width-1):0] sva_w_data;

  integer m;

  assign sva_w_data = sva_v_q[sva_v_head_ptr];



  always @ (posedge clk) begin
    if (`OVL_RESET_SIGNAL != 1'b1) begin
      preload_reg <= 1'b1;

//Initialize queue in reset block so that the implementation is formal friendly
      for (i=0;i<depth;i=i+1) begin
       sva_v_q[i] = {width{1'b0}};
      end
    end
    else begin
      if (preload_reg == 1'b1) begin
        for (m = 0; m < preload_count; m=m+1) begin
      sva_v_q[m] <= preload[((m+1)*width)-1 -: width];
        end
        preload_reg <= 1'b0;
      end

      if( sva_v_deferred_enq &&
          !((sva_v_q_size == 0) && pass_thru &&
          sva_v_deferred_deq) &&
          !((sva_v_q_size == depth) &&
             (!sva_v_deferred_deq || (sva_v_deferred_deq && !registered))) )  begin
        sva_v_q[sva_v_tail_ptr] <= enq_data;
      end
      else begin
    if (preload_reg == 1'b0)
          sva_v_q[sva_v_tail_ptr] <= sva_v_q[sva_v_tail_ptr];
      end
    end
  end

  property OVL_FIFO_VALUE_P;
    @ (posedge clk)
      disable iff(`OVL_RESET_SIGNAL != 1'b1)
    sva_v_deferred_deq |->((sva_v_q_size == 0)?
              (!pass_thru?
               1:!sva_v_deferred_enq?
               1:(enq_data==deq_data)):
              (sva_v_q_size == depth)?
              ((!registered && sva_v_deferred_enq)?
               1:sva_w_data == deq_data):
              sva_w_data == deq_data);
  endproperty

  property OVL_FIFO_OVERFLOW_P;
    @ (posedge clk)
      disable iff(`OVL_RESET_SIGNAL != 1'b1)
        not ((sva_v_q_size >= depth) &&
             sva_v_deferred_enq &&
             (!sva_v_deferred_deq || !registered));
  endproperty

  property OVL_FIFO_UNDERFLOW_P;
    @ (posedge clk)
      disable iff(`OVL_RESET_SIGNAL != 1'b1)
        not ((sva_v_q_size == 0) &&
             (!( sva_v_deferred_enq && pass_thru)) &&
             sva_v_deferred_deq);
  endproperty

  property OVL_FIFO_FULL_P;
    @ (posedge clk)
      disable iff(`OVL_RESET_SIGNAL != 1'b1)
        (fifo_full == full);
  endproperty

  property OVL_FIFO_EMPTY_P;
    @ (posedge clk)
      disable iff(`OVL_RESET_SIGNAL != 1'b1)
        (fifo_empty == empty);
  endproperty

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else

    property OVL_FIFO_XZ_ON_ENQ_P;
    @ (posedge clk)
      disable iff(`OVL_RESET_SIGNAL != 1'b1)
        (!($isunknown(enq)));
    endproperty

    property OVL_FIFO_XZ_ON_DEQ_P;
    @ (posedge clk)
      disable iff(`OVL_RESET_SIGNAL != 1'b1)
        (!($isunknown(deq)));
    endproperty

    property OVL_FIFO_XZ_ON_FULL_P;
    @ (posedge clk)
      disable iff(`OVL_RESET_SIGNAL != 1'b1)
        (!($isunknown(full)));
    endproperty

    property OVL_FIFO_XZ_ON_EMPTY_P;
    @ (posedge clk)
      disable iff(`OVL_RESET_SIGNAL != 1'b1)
        (!($isunknown(empty)));
    endproperty

    property OVL_FIFO_XZ_ON_ENQ_DATA_P;
    @ (posedge clk)
      disable iff(`OVL_RESET_SIGNAL != 1'b1)
       sva_v_deferred_enq  |-> (!($isunknown(enq_data)));
    endproperty

    property OVL_FIFO_XZ_ON_DEQ_DATA_P;
    @ (posedge clk)
      disable iff(`OVL_RESET_SIGNAL != 1'b1)
        sva_v_deferred_deq |-> (!($isunknown(deq_data)));
    endproperty

  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

  generate
    case (property_type)
      `OVL_ASSERT_2STATE,
      `OVL_ASSERT: begin : ovl_assert

        if(value_check) begin : value_check
          A_OVL_FIFO_VALUE_P:
          assert property (OVL_FIFO_VALUE_P)
          else begin
            ovl_error_t(`OVL_FIRE_2STATE,"Dequeued FIFO value did not equal the corresponding enqueued value");
            error_event = 1;
          end
        end : value_check

          A_OVL_FIFO_OVERFLOW_P:
          assert property (OVL_FIFO_OVERFLOW_P)
          else begin
            ovl_error_t(`OVL_FIRE_2STATE,"Enqueue occurred that would overflow the FIFO");
            error_event = 1;
          end

          A_OVL_FIFO_UNDERFLOW_P:
          assert property (OVL_FIFO_UNDERFLOW_P)
          else begin
            ovl_error_t(`OVL_FIRE_2STATE,"Dequeue occurred that would underflow the FIFO");
            error_event = 1;
          end

          A_OVL_FIFO_FULL_P:
          assert property (OVL_FIFO_FULL_P)
          else begin
            ovl_error_t(`OVL_FIRE_2STATE,"FIFO `full' signal asserted or deasserted in the wrong cycle");
            error_event = 1;
          end

          A_OVL_FIFO_EMPTY_P:
          assert property (OVL_FIFO_EMPTY_P)
          else begin
            ovl_error_t(`OVL_FIRE_2STATE,"FIFO `empty' signal asserted or deasserted in the wrong cycle");
            error_event = 1;
          end

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else

        A_OVL_FIFO_XZ_ON_ENQ_P:
        assert property (OVL_FIFO_XZ_ON_ENQ_P)
        else begin
          ovl_error_t(`OVL_FIRE_XCHECK,"enq contains X or Z");
          error_event_xz = 1;
        end

        A_OVL_FIFO_XZ_ON_DEQ_P:
        assert property (OVL_FIFO_XZ_ON_DEQ_P)
        else begin
          ovl_error_t(`OVL_FIRE_XCHECK,"deq contains X or Z");
          error_event_xz = 1;
        end

        A_OVL_FIFO_XZ_ON_FULL_P:
        assert property (OVL_FIFO_XZ_ON_FULL_P)
        else begin
          ovl_error_t(`OVL_FIRE_XCHECK,"full contains X or Z");
          error_event_xz = 1;
        end

        A_OVL_FIFO_XZ_ON_EMPTY_P:
        assert property (OVL_FIFO_XZ_ON_EMPTY_P)
        else begin
          ovl_error_t(`OVL_FIRE_XCHECK,"empty contains X or Z");
          error_event_xz = 1;
        end

        A_OVL_FIFO_XZ_ON_ENQ_DATA_P:
        assert property (OVL_FIFO_XZ_ON_ENQ_DATA_P)
        else begin
          ovl_error_t(`OVL_FIRE_XCHECK,"enq_data contains X or Z");
          error_event_xz = 1;
        end

        A_OVL_FIFO_XZ_ON_DEQ_DATA_P:
        assert property (OVL_FIFO_XZ_ON_DEQ_DATA_P)
        else begin
          ovl_error_t(`OVL_FIRE_XCHECK,"deq_data contains X or Z");
          error_event_xz = 1;
        end

  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

      end

      `OVL_ASSUME_2STATE,
      `OVL_ASSUME: begin : ovl_assume

        if(value_check) begin : value_check
          M_OVL_FIFO_VALUE_P:
          assume property (OVL_FIFO_VALUE_P);
        end : value_check

          M_OVL_FIFO_OVERFLOW_P:
          assume property (OVL_FIFO_OVERFLOW_P);

          M_OVL_FIFO_UNDERFLOW_P:
          assume property (OVL_FIFO_UNDERFLOW_P);

          M_OVL_FIFO_FULL_P:
          assume property (OVL_FIFO_FULL_P);

          M_OVL_FIFO_EMPTY_P:
          assume property (OVL_FIFO_EMPTY_P);

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else

        M_OVL_FIFO_XZ_ON_ENQ_P:
        assume property (OVL_FIFO_XZ_ON_ENQ_P);

        M_OVL_FIFO_XZ_ON_DEQ_P:
        assume property (OVL_FIFO_XZ_ON_DEQ_P);

        M_OVL_FIFO_XZ_ON_FULL_P:
        assume property (OVL_FIFO_XZ_ON_FULL_P);

        M_OVL_FIFO_XZ_ON_EMPTY_P:
        assume property (OVL_FIFO_XZ_ON_EMPTY_P);

        M_OVL_FIFO_XZ_ON_ENQ_DATA_P:
        assume property (OVL_FIFO_XZ_ON_ENQ_DATA_P);

        M_OVL_FIFO_XZ_ON_DEQ_DATA_P:
        assume property (OVL_FIFO_XZ_ON_DEQ_DATA_P);

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

 `ifdef OVL_COVERGROUP_ON
  covergroup fifo_contents_cg @(posedge clk);
  coverpoint int'( sva_v_q_size)
    iff(`OVL_RESET_SIGNAL != 1'b0 &&
        past_sva_v_q_size != sva_v_q_size) {
        bins observed_fifo_contents[] = {[0:depth]};
      }
    option.per_instance = 1;
    option.at_least = 1;
    option.name = "observed_contents";
    option.comment = "Bin index is the observed fill level";
  endgroup : fifo_contents_cg
 `endif //  `ifdef OVL_COVERGROUP_ON

  generate

    if (coverage_level != `OVL_COVER_NONE) begin : ovl_cover

      if (OVL_COVER_SANITY_ON) begin : ovl_cover_sanity

        cover_enqueues :
          cover property(
            @(posedge clk)
             ((`OVL_RESET_SIGNAL != 1'b0) && enq))
        ovl_cover_t("Enqueue is performed");

        cover_dequeues :
          cover property(
            @(posedge clk)
              ((`OVL_RESET_SIGNAL != 1'b0) && deq))
        ovl_cover_t("Dequeue is performed");

      end : ovl_cover_sanity

      if (OVL_COVER_BASIC_ON) begin : ovl_cover_basic

        cover_simultaneous_enq_deq :
          cover property(
            @(posedge clk)
              ((`OVL_RESET_SIGNAL != 1'b0) && enq && deq))
        ovl_cover_t("Enqueue and Dequeue both have come simultaneously");

    cover_enq_followed_by_deq :
          cover property(
          @(posedge clk)
            (`OVL_RESET_SIGNAL != 1'b0) throughout (
              ( pass_thru && enq && deq && sva_v_q_size == 0) or (registered && enq && deq && sva_v_q_size == depth) or
                  ( enq ##1 !enq[*1:$] ##0 deq)))
        ovl_cover_t("Enqueue is followed by dequeue");

        cover_enq_followed_eventually_by_deq :
          cover property(
          @(posedge clk)
            (`OVL_RESET_SIGNAL != 1'b0) throughout (
              ( pass_thru && enq && deq && sva_v_q_size == 0) or (registered && enq && deq && sva_v_q_size == depth) or
                 first_match( enq ##1 !enq[*1:$] ##0 deq)))
        ovl_cover_t("Enqueue is followed by dequeue");

      end : ovl_cover_basic

      if (OVL_COVER_STATISTIC_ON) begin : ovl_cover_statistic

 `ifdef OVL_COVERGROUP_ON

    fifo_contents_cg cover_observed_contents;
    initial begin
      if (OVL_COVER_STATISTIC_ON) begin
        cover_observed_contents = new();
      end
    end
        
 `endif

      end : ovl_cover_statistic

      if (OVL_COVER_CORNER_ON) begin : ovl_cover_corner

        if (high_water_mark > 0) begin : high_water_mark_check
          cover_high_water_mark :
            cover property(
              @(posedge clk)
               (`OVL_RESET_SIGNAL != 1'b0) && (sva_v_q_size >= high_water_mark) &&
                (!sva_v_hi_water_failed))
          ovl_cover_t("fifo occupancy is above high water mark specified");
        end : high_water_mark_check

    cover_simultaneous_enq_deq_when_empty :
          cover property(
            @(posedge clk)
              ((`OVL_RESET_SIGNAL != 1'b0) && sva_v_deferred_enq &&
                 sva_v_deferred_deq && (sva_v_q_size == 0)))
        ovl_cover_t("simultaneous enq and deq detected while fifo is empty");

    cover_simultaneous_enq_deq_when_full :
          cover property(
            @(posedge clk)
              ((`OVL_RESET_SIGNAL != 1'b0) && sva_v_deferred_enq &&
                sva_v_deferred_deq && (sva_v_q_size == depth)))
        ovl_cover_t("simultaneous enq and deq detected while fifo is full");

        cover_number_of_empty :
          cover property(
            @(posedge clk)
              (`OVL_RESET_SIGNAL != 1'b0) throughout(
            sva_v_deferred_deq ##1
              (!$stable( sva_v_q_size || (pass_thru && $past(sva_v_deferred_enq))) &&
             (sva_v_q_size ==0))))
        ovl_cover_t("fifo is empty");

    cover_number_of_full :
          cover property(
            @(posedge clk)
              (`OVL_RESET_SIGNAL != 1'b0) throughout(
            sva_v_deferred_enq ##1
                  ((!$stable( sva_v_q_size) || (registered && $past(sva_v_deferred_deq))) &&
                   sva_v_q_size ==depth)))
        ovl_cover_t("fifo is full");

      end : ovl_cover_corner

    end : ovl_cover

  endgenerate

`endif // OVL_COVER_ON
