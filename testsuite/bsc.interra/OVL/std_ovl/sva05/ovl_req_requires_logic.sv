// Accellera Standard V2.8.1 Open Verification Library (OVL).
// Accellera Copyright (c) 2005-2014. All rights reserved.


  bit error_event, error_event_xz;

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

  sequence sva_s_req_trigger_req_follower;
    ( req_trigger ##0 ((!req_follower[*0:$]) ##1 req_follower));
  endsequence

  sequence sva_s_req_trigger_req_follower_resp_leader;
    ( sva_s_req_trigger_req_follower ##1
       (!resp_leader[*0:$]) ##1 resp_leader);
  endsequence

  sequence sva_s_req_trigger_req_follower_resp_leader_resp_trigger;
     ( sva_s_req_trigger_req_follower_resp_leader ##0
        ((!resp_trigger[*0:$]) ##1 resp_trigger));
  endsequence

`ifdef OVL_SYNTHESIS
`else
  generate
    if ((max_cks < 0) || ((max_cks > 0) && (min_cks > max_cks))) begin : max_l_0
          initial $display("Illegal max_cks parameter value < 0");
    end : max_l_0
    if (min_cks <= 0) begin : min_l_e_0
      initial $display("Illegal min_cks parameter value <= 0");
    end : min_l_e_0
  endgenerate
`endif

`endif // OVL_SHARED_CODE

`ifdef OVL_ASSERT_ON

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else

    property OVL_REQ_REQUIRES_XZ_ON_TRIG_REQ_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    (!($isunknown(req_trigger)));
    endproperty

    property OVL_REQ_REQUIRES_XZ_ON_FOLLOW_REQ_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    (!($isunknown(req_follower)));
    endproperty

    property OVL_REQ_REQUIRES_XZ_ON_FOLLOW_RESP_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    (!($isunknown(resp_leader)));
    endproperty

    property OVL_REQ_REQUIRES_XZ_ON_TRIG_RESP_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    (!($isunknown(resp_trigger)));
    endproperty

  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

  generate
    case (property_type)
      `OVL_ASSERT_2STATE,
      `OVL_ASSERT: begin : ovl_assert

        if (min_cks > 0) begin : min_g_0
          if ((max_cks > 0) && (min_cks <= max_cks)) begin : max_g_0

            property OVL_REQ_REQUIRES_CASE1_P;     // min_cks > 0 and max_cks > 0
             @(posedge clk)
              disable iff(`OVL_RESET_SIGNAL != 1'b1)
              ( req_trigger |->
              ( ( ( 1'b1) [*min_cks+1:max_cks+1]) intersect
              ( sva_s_req_trigger_req_follower_resp_leader_resp_trigger)));
            endproperty

            A_OVL_REQ_REQUIRES_CASE1_P:
            assert property (OVL_REQ_REQUIRES_CASE1_P)
            else begin
              ovl_error_t(`OVL_FIRE_2STATE,"After req_trigger asserted specified sequence did not occur within min to max latency");
              error_event = 1;
            end
          end : max_g_0
          else if (max_cks == 0) begin : max_e_0

            property OVL_REQ_REQUIRES_CASE2_P;    // min_cks > 0 and max_cks == 0
             @(posedge clk)
              disable iff(`OVL_RESET_SIGNAL != 1'b1)
              ( req_trigger |->
              ( ( ( 1'b1) [*min_cks+1:$]) intersect
              ( sva_s_req_trigger_req_follower_resp_leader_resp_trigger)));
            endproperty

            A_OVL_REQ_REQUIRES_CASE2_P:
            assert property (OVL_REQ_REQUIRES_CASE2_P)
            else begin
              ovl_error_t(`OVL_FIRE_2STATE,"After req_trigger asserted specified sequence did not occur within min to max latency");
              error_event = 1;
            end
          end : max_e_0
    end : min_g_0

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else

        A_OVL_REQ_REQUIRES_XZ_ON_TRIG_REQ_P:
        assert property (OVL_REQ_REQUIRES_XZ_ON_TRIG_REQ_P)
        else begin
          ovl_error_t(`OVL_FIRE_XCHECK,"req_trigger contains X or Z");
          error_event_xz = 1;
        end

        A_OVL_REQ_REQUIRES_XZ_ON_FOLLOW_REQ_P:
        assert property (OVL_REQ_REQUIRES_XZ_ON_FOLLOW_REQ_P)
        else begin
          ovl_error_t(`OVL_FIRE_XCHECK,"req_follower contains X or Z");
          error_event_xz = 1;
        end

        A_OVL_REQ_REQUIRES_XZ_ON_FOLLOW_RESP_P:
        assert property (OVL_REQ_REQUIRES_XZ_ON_FOLLOW_RESP_P)
        else begin
          ovl_error_t(`OVL_FIRE_XCHECK,"resp_leader contains X or Z");
          error_event_xz = 1;
        end

        A_OVL_REQ_REQUIRES_XZ_ON_TRIG_RESP_P:
        assert property (OVL_REQ_REQUIRES_XZ_ON_TRIG_RESP_P)
        else begin
          ovl_error_t(`OVL_FIRE_XCHECK,"resp_trigger contains X or Z");
          error_event_xz = 1;
        end

  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

      end

      `OVL_ASSUME_2STATE,
      `OVL_ASSUME: begin : ovl_assume

        if (min_cks > 0) begin : min_g_0
          if ((max_cks > 0) && (min_cks <= max_cks)) begin : max_g_0

            property OVL_REQ_REQUIRES_CASE1_P;     // min_cks > 0 and max_cks > 0
             @(posedge clk)
             disable iff(`OVL_RESET_SIGNAL != 1'b1)
             ( req_trigger |->
             ( ( ( 1'b1) [*min_cks+1:max_cks+1]) intersect
             ( sva_s_req_trigger_req_follower_resp_leader_resp_trigger)));
            endproperty

            M_OVL_REQ_REQUIRES_CASE1_P:
            assume property (OVL_REQ_REQUIRES_CASE1_P);
          end : max_g_0
          else if (max_cks == 0) begin : max_e_0

            property OVL_REQ_REQUIRES_CASE2_P;    // min_cks > 0 and max_cks == 0
             @(posedge clk)
              disable iff(`OVL_RESET_SIGNAL != 1'b1)
              ( req_trigger |->
              ( ( ( 1'b1) [*min_cks+1:$]) intersect
              ( sva_s_req_trigger_req_follower_resp_leader_resp_trigger)));
            endproperty

            M_OVL_REQ_REQUIRES_CASE2_P:
            assume property (OVL_REQ_REQUIRES_CASE2_P);
          end : max_e_0
    end : min_g_0

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else

        M_OVL_REQ_REQUIRES_XZ_ON_TRIG_REQ_P:
        assume property (OVL_REQ_REQUIRES_XZ_ON_TRIG_REQ_P);

        M_OVL_REQ_REQUIRES_XZ_ON_FOLLOW_REQ_P:
        assume property (OVL_REQ_REQUIRES_XZ_ON_FOLLOW_REQ_P);

        M_OVL_REQ_REQUIRES_XZ_ON_FOLLOW_RESP_P:
        assume property (OVL_REQ_REQUIRES_XZ_ON_FOLLOW_RESP_P);

        M_OVL_REQ_REQUIRES_XZ_ON_TRIG_RESP_P:
        assume property (OVL_REQ_REQUIRES_XZ_ON_TRIG_RESP_P);

  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

      end

      `OVL_IGNORE : begin : ovl_ignore
        // do nothing;
      end
      default     : begin
`ifndef OVL_SYNTHESIS
             initial ovl_error_t(`OVL_FIRE_2STATE,"");
`endif
      end
    endcase
  endgenerate

`endif // OVL_ASSERT_ON


`ifdef OVL_COVER_ON

`ifdef OVL_COVERGROUP_ON

  localparam d_max_cks = max_cks < 1? 4095 : max_cks;

  // req_trigger_resp_trigger_latency_cg cover group

  int cnt_req_trigger_resp_trigger  = 0;

  always @ (posedge clk) begin
    if(`OVL_RESET_SIGNAL != 1'b1) begin
      cnt_req_trigger_resp_trigger  <= 0;
    end
    else begin
      if( req_trigger) begin
        cnt_req_trigger_resp_trigger  <= 1;
      end
      else if( cnt_req_trigger_resp_trigger>0) begin    
        cnt_req_trigger_resp_trigger  <= cnt_req_trigger_resp_trigger+1;
      end
    end
  end

  covergroup req_trigger_resp_trigger_latency_cg @(posedge clk);
    coverpoint cnt_req_trigger_resp_trigger
      iff( (`OVL_RESET_SIGNAL != 1'b0) && resp_trigger &&
        ( cnt_req_trigger_resp_trigger >= 0)) {
          bins observed_req_trigger_resp_trigger_latency_good[] = {[min_cks:d_max_cks]};
          bins observed_req_trigger_resp_trigger_latency_bad = default;
      }
      option.per_instance = 1;
      option.at_least = 1;
      option.name = "observed_latency_btw_req_trigger_and_resp_trigger";
      option.comment = "Bin index is the observed latency between <req_trigger> and <resp_trigger>";
  endgroup : req_trigger_resp_trigger_latency_cg

  // req_trigger_req_follower_latency_cg cover group

  int cnt_req_trigger_foll_req   = 0;

  always @ (posedge clk) begin
    if(`OVL_RESET_SIGNAL != 1'b1) begin
      cnt_req_trigger_foll_req   <= 0;
    end
    else begin
      if( req_trigger) begin
        cnt_req_trigger_foll_req   <= 1;
      end
      else if( cnt_req_trigger_foll_req>0) begin    
        cnt_req_trigger_foll_req   <= cnt_req_trigger_foll_req+1;
      end
    end
  end

  covergroup req_trigger_req_follower_latency_cg @(posedge clk);
    coverpoint ( req_trigger ? 0 : cnt_req_trigger_foll_req)
      iff( (`OVL_RESET_SIGNAL != 1'b0) && req_follower &&
        cnt_req_trigger_foll_req>=0) {
            bins observed_req_trigger_req_follower_latency_good[] = {[0:d_max_cks]};
            bins observed_req_trigger_req_follower_latency_bad = default;
      }
      option.per_instance = 1;
      option.at_least = 1;
      option.name = "observed_latency_btw_req_trigger_and_req_follower";
      option.comment = "Bin index is the observed latency between <req_trigger> and <req_follower>";
  endgroup : req_trigger_req_follower_latency_cg

  // req_follower_resp_leader_latency_cg cover group

  int cnt_foll_req_foll_resp  = 0;

  always @ (posedge clk) begin
    if(`OVL_RESET_SIGNAL != 1'b1) begin
       cnt_foll_req_foll_resp  <= 0;
    end
    else begin
      if( req_follower) begin
        cnt_foll_req_foll_resp  <= 1;
      end
      else if( cnt_foll_req_foll_resp>0) begin
        cnt_foll_req_foll_resp  <= cnt_foll_req_foll_resp+1;
      end    
    end
  end

  covergroup req_follower_resp_leader_latency_cg @(posedge clk);
    coverpoint ( req_follower ? 0 : cnt_foll_req_foll_resp)
      iff( (`OVL_RESET_SIGNAL != 1'b0) && resp_leader &&
          cnt_foll_req_foll_resp>=0) {
        bins observed_req_follower_resp_leader_latency_good[] = {[1:d_max_cks]};
        bins observed_req_follower_resp_leader_latency_bad = default;
      }
      option.per_instance = 1;
      option.at_least = 1;
      option.name = "observed_latency_btw_req_follower_and_resp_leader";
      option.comment = "Bin index is the observed latency between <req_follower> and <resp_leader>";
  endgroup : req_follower_resp_leader_latency_cg


  // resp_leader_resp_trigger_latency_cg cover group

  int cnt_foll_resp_resp_trigger = 0;

  always @ (posedge clk) begin
    if(`OVL_RESET_SIGNAL != 1'b1) begin
      cnt_foll_resp_resp_trigger <= 0;
    end
    else begin
      if( resp_leader) begin
        cnt_foll_resp_resp_trigger <= 1;
      end    
      else if( cnt_foll_resp_resp_trigger>0) begin
        cnt_foll_resp_resp_trigger <= cnt_foll_resp_resp_trigger+1;
      end
    end
  end

  covergroup resp_leader_resp_trigger_latency_cg @(posedge clk);
    coverpoint ( resp_leader ? 0 : cnt_foll_resp_resp_trigger)
      iff( (`OVL_RESET_SIGNAL != 1'b0) && resp_trigger &&
           cnt_foll_resp_resp_trigger >= 0) {
         bins observed_resp_leader_resp_trigger_latency_good[] = {[0:d_max_cks]};
         bins observed_resp_leader_resp_trigger_latency_bad = default;
      }
      option.per_instance = 1;
      option.at_least = 1;
      option.name = "observed_latency_btw_resp_leader_and_resp_trigger";
      option.comment = "Bin index is the observed latency between <resp_leader> and <resp_trigger>";
  endgroup : resp_leader_resp_trigger_latency_cg

`endif  // `ifdef OVL_COVERGROUP_ON

  generate

    if (coverage_level != `OVL_COVER_NONE) begin : ovl_cover

      if (OVL_COVER_SANITY_ON) begin : ovl_cover_sanity

        cover_num_of_req_triggers:
          cover property( @(posedge clk) req_trigger)
          ovl_cover_t("req_trigger input asserted");

      end : ovl_cover_sanity

      if (OVL_COVER_BASIC_ON) begin : ovl_cover_basic

        if (min_cks > 0) begin : min_g_0
          if (max_cks > 0) begin : max_g_0
            cover_req_requires:
              cover property(
                @(posedge clk)
                  ( (`OVL_RESET_SIGNAL != 1'b0) [*min_cks+1:max_cks+1]) intersect
                    ( sva_s_req_trigger_req_follower_resp_leader_resp_trigger))
              ovl_cover_t("Specified sequence occured");

            cover_req_trigger_req_follower:
              cover property(
                @(posedge clk)
                  ((`OVL_RESET_SIGNAL != 1'b0) [*1:max_cks]) intersect sva_s_req_trigger_req_follower)
              ovl_cover_t("req_follower asserted after req_trigger");

            cover_req_trigger_req_follower_resp_leader:
              cover property(
                @(posedge clk)
                 ((`OVL_RESET_SIGNAL != 1'b0) [*2:max_cks+1]) intersect
                ( sva_s_req_trigger_req_follower_resp_leader))
              ovl_cover_t("There was a req_follower after req_trigger followed by resp_leader");

          end : max_g_0
          else if (max_cks == 0) begin : max_e_0
            cover_req_requires:
              cover property(
                @(posedge clk)
                  ( (`OVL_RESET_SIGNAL != 1'b0) [*min_cks+1:$]) intersect
                    ( sva_s_req_trigger_req_follower_resp_leader_resp_trigger))
              ovl_cover_t("Specified sequence occured");

            cover_req_trigger_req_follower:
              cover property(
                @(posedge clk)
                  ((`OVL_RESET_SIGNAL != 1'b0) [*1:$]) intersect sva_s_req_trigger_req_follower)
              ovl_cover_t("req_follower asserted after req_trigger");

            cover_req_trigger_req_follower_resp_leader:
              cover property(
                @(posedge clk)
                 ((`OVL_RESET_SIGNAL != 1'b0) [*2:$]) intersect
                ( sva_s_req_trigger_req_follower_resp_leader))
              ovl_cover_t("There was a req_follower after req_trigger followed by resp_leader");

          end : max_e_0
        end : min_g_0

      end : ovl_cover_basic

      if (OVL_COVER_STATISTIC_ON) begin : ovl_cover_statistic

`ifdef OVL_COVERGROUP_ON

        req_trigger_resp_trigger_latency_cg      cover_latency_btw_req_trigger_and_resp_trigger     = new();

        req_trigger_req_follower_latency_cg     cover_latency_btw_req_trigger_and_req_follower    = new();

        req_follower_resp_leader_latency_cg  cover_latency_btw_req_follower_and_resp_leader = new();

        resp_leader_resp_trigger_latency_cg   cover_latency_btw_resp_leader_and_resp_trigger  = new();

`endif

      end : ovl_cover_statistic

      if (OVL_COVER_CORNER_ON) begin : ovl_cover_corner

        if (min_cks >0) begin : min_g_0
      cover_resp_trigger_exactly_on_min_cks:
            cover property(
              @(posedge clk)
                ( (`OVL_RESET_SIGNAL != 1'b0) [*min_cks+1]) intersect
                  ( sva_s_req_trigger_req_follower_resp_leader_resp_trigger))
          ovl_cover_t("Sequence occurred exactly in min_cks number of clock cycles");
        end : min_g_0
        if (max_cks > 0) begin : max_g_0
      cover_resp_trigger_exactly_on_max_cks:
            cover property(
              @(posedge clk)
                ( (`OVL_RESET_SIGNAL != 1'b0) [*max_cks+1]) intersect
                  ( sva_s_req_trigger_req_follower_resp_leader_resp_trigger))
          ovl_cover_t("Sequence occurred exactly in max_cks number of clock cycles");
        end : max_g_0

      end : ovl_cover_corner

    end : ovl_cover

  endgenerate

`endif // OVL_COVER_ON
