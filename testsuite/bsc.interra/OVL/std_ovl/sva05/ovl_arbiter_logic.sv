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

  localparam  fairness_chk = (arbitration_rule == 1);
  localparam  fifo_chk     = (arbitration_rule == 2);
  localparam  lru_chk      = (arbitration_rule == 3);


  reg [width-1:0]  past_reqs    = {width{1'b0}};
  reg [width-1:0]  past_gnts  = {width{1'b0}};
  reg [width-1:0]  granted_once = {width{1'b0}};

  integer  k1, k2, k3, k4, k5, k6, l1, l2, m, b;
  genvar   i, j, n, gen_chnl;

  reg  [priority_width-1:0] highest [width-1 : 0];
  reg  [priority_width-1:0] pre_highest[0:min_cks];

`ifdef OVL_SYNTHESIS
`else
  initial begin
    for (b = 0; b <= min_cks; b=b+1)
      pre_highest[b] = {priority_width{1'b0}};

    for (b = 0; b < width; b=b+1)
      highest[b] = {priority_width{1'b0}};
  end
`endif

  // granted to highest priorities
  always @(*)  begin
     highest[0] = reqs[0] ?
                   priorities[priority_width-1:0] : 0;
     for( k1 = 1; k1<width; k1 = k1+1) begin
        highest[k1] = reqs[k1] &&
          (priorities[priority_width*k1 +: priority_width] >
             highest[k1-1]) ?
               priorities[priority_width*k1 +: priority_width] :
                 highest[k1-1];
     end
  end // always @ ( *)

  always @ (posedge clk) begin
    past_reqs        <= reqs;
    past_gnts      <= gnts;

     if (`OVL_RESET_SIGNAL != 1'b1)
        granted_once <= 0;
     else
        granted_once <= granted_once | gnts;
  end

  generate
    if(min_cks > 0) begin : min_cks_g_0
       always @(posedge clk) begin
          pre_highest[1] <= (`OVL_RESET_SIGNAL != 1'b0) ?
            highest[width-1] : {priority_width{1'b0}};
          for (m = 2;  m<=min_cks; m = m+1) begin
             pre_highest[m] <= (`OVL_RESET_SIGNAL != 1'b0) ?
               pre_highest[m-1] : {priority_width{1'b0}};
          end
       end
    end : min_cks_g_0
    else
       always @(*) pre_highest[min_cks] = highest[width-1];
  endgenerate

    //stack of past gnts encoded in unary
      reg [width-1:0] lru_r [0:width-1];

`ifdef OVL_SYNTHESIS
`else
      initial begin
        for (b = 0; b < width; b=b+1)
          lru_r[b] = {width{1'b0}};
      end
`endif

    //highest priority requests
      reg [width-1:0] highest_reqs = {width{1'b0}};

    //highest priority lines
      reg [width-1:0] highest_bits = {width{1'b0}};

    // select stack rows for shift
      reg [width-1:0] shift = {width{1'b0}};

    //indicates the lru entry in stack
      reg [width-1:0] found_gnts = {width{1'b0}};

    // enable for loading lru_r
      reg [width-1 : 0] load [width-1 : 0];

      reg [width-1:0] selected_gnts [0:width-1];

`ifdef OVL_SYNTHESIS
`else
      initial begin
        for (b = 0; b < width; b=b+1) begin
          selected_gnts[b] = {width{1'b0}};
          load[b]            = {width{1'b0}};
        end
      end
`endif

    // predicted grant(s)
    // in selected_gnts[width-1]
    // initially can be more than one, arbitrary choice

      wire [width-1:0] predicted_gnts;
      assign predicted_gnts = selected_gnts[width-1];

// determine lines with highest priority, all if priority not enabled

      always @(*) begin
         for(l1=0; l1<width; l1=l1+1)
            highest_bits[l1] =
               (priorities[priority_width*l1 +: priority_width] ==
                    pre_highest[min_cks])
               |
               (!priority_check);

// highest priority actual requests

          highest_reqs = highest_bits & reqs;
      end

// find which rows in stack should be pushed (shifted)
// given current gnts

      always @(*) begin
         shift[width-1] = |(gnts &
                              (lru_r[width-1] | ~granted_once));
         for (k2=width-2; k2>=0; k2=k2-1)
            shift[k2] = (|(gnts & lru_r[k2])) || shift[k2+1];
      end

// compute which bits in stack lru_r should be pushed (shifted)

      always @(*)
         for (k3=0; k3<width; k3=k3+1) begin : rows
            reg [width-1:0] temp;
            for (l2=0; l2<width; l2=l2+1) begin
               temp[l2] = shift[k3] && highest_bits[l2];
            end
            load[k3] = temp;
         end

// determine position (row) in stack that has lru grant or
// never granted

      always @(*) begin
        found_gnts[width-1] = |(highest_reqs & (lru_r[width-1] | ~granted_once));

        for (k4=width-2; k4>=0; k4=k4-1)
          found_gnts[k4] = (|(highest_reqs & lru_r[k4])) || found_gnts[k4+1];
      end

// compute effective grant prediction row and column
// selected_gnts[width-1] contains the predicet grant(s)
// until all gnts lines have been issued there could be more
// than one predicted since initially all are at -infinity

      always @(*) begin
         selected_gnts[0] = found_gnts[1] ? 0 :
                                    highest_reqs & lru_r[0];
         for (k5=1; k5<width-1; k5=k5+1)
           selected_gnts[k5] = (found_gnts[k5+1] ? 0 : highest_reqs & lru_r[k5]) |
                                selected_gnts[k5-1];
         selected_gnts[width-1] = (highest_reqs & (lru_r[width-1] | ~granted_once)) |
                                       selected_gnts[width-2];
      end

// update stack, position 0 is loaded by current grant vector if enabled
// others just shift if the position is enabled

      always @(posedge clk) begin
        if (`OVL_RESET_SIGNAL != 1'b1)
          for (k6=0; k6<width; k6=k6+1) lru_r[k6] <= 0;
        else begin
          lru_r[0] <= (load[0] & gnts) | (~load[0] & lru_r[0]);

          for (m=1; m<width; m=m+1) begin
            lru_r[m] <= (load[m] & lru_r[m-1]) | (~load[m] & lru_r[m]);
          end
        end
      end

`endif // OVL_SHARED_CODE

`ifdef OVL_ASSERT_ON

  `ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else

    property OVL_ARBITER_XZ_ON_REQS_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    (!($isunknown(reqs)));
    endproperty

    property OVL_ARBITER_XZ_ON_GNTS_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    (!($isunknown(gnts)));
    endproperty

    property OVL_ARBITER_XZ_ON_PRIORITIES_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    (!($isunknown(priorities)));
    endproperty

  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

  generate
    case (property_type)
      `OVL_ASSERT,`OVL_ASSUME : begin : ovl_assert_assume

        if (priority_check && (min_cks >= 0)) begin : priorities_check

          for( n = 0; n< width; n=n+1) begin : loop_min_cks_gt_0
            property OVL_ARBITER_HIGHEST_PRIORITY_P;
              @(posedge clk)
                disable iff(`OVL_RESET_SIGNAL != 1'b1)
                  (gnts[n]) |->
                    (priorities[priority_width*(n+1)-1 : priority_width*n] ==
                      pre_highest[min_cks]);
            endproperty

            if (property_type == `OVL_ASSERT) begin
              A_OVL_ARBITER_HIGHEST_PRIORITY_P:
              assert property (OVL_ARBITER_HIGHEST_PRIORITY_P)
              else begin
                ovl_error_t(`OVL_FIRE_2STATE,"Grant was issued for a request other than the highest priority request");
                error_event = 1;
              end
            end
            else begin
              M_OVL_ARBITER_HIGHEST_PRIORITY_P:
              assume property (OVL_ARBITER_HIGHEST_PRIORITY_P);
            end

          end : loop_min_cks_gt_0
        end : priorities_check

        for( i = 0; i < width; i = i+1) begin : loop_A

          // a non-cancelled req is eventually granted
          // within allowed latency

          if ((max_cks > 0) && (min_cks > 0)) begin : min_g_0_max_g_0
            property OVL_ARBITER_GNT_IN_WINDOW_P;
              @(posedge clk)
                disable iff(`OVL_RESET_SIGNAL != 1'b1)
                  ( ((!reqs[i])|| gnts[i]) ##1
                    reqs[i]) |->
                      ( ##[min_cks:max_cks] (gnts[i] || //OK
                                            !reqs[i])  //cancel req
                    ) and
                    ((!gnts[i])[*min_cks]);
            endproperty

            if (property_type == `OVL_ASSERT) begin
              A_OVL_ARBITER_GNT_IN_WINDOW_P:
              assert property (OVL_ARBITER_GNT_IN_WINDOW_P)
              else begin
                ovl_error_t(`OVL_FIRE_2STATE,"Grant was not issued within the specified time window");
                error_event = 1;
              end
            end
            else begin
              M_OVL_ARBITER_GNT_IN_WINDOW_P:
              assume property (OVL_ARBITER_GNT_IN_WINDOW_P);
            end

          end : min_g_0_max_g_0

          if ((max_cks > 0) && (min_cks == 0)) begin : min_e_0_max_g_0
            property OVL_ARBITER_GNT_IN_WINDOW_P;
                @(posedge clk)
                   disable iff(`OVL_RESET_SIGNAL != 1'b1)
                     (((!reqs[i])|| gnts[i]) ##1
                       reqs[i]) |->
                         ##[0:max_cks] (gnts[i] || //OK
                                      !reqs[i]); //cancel req
            endproperty

            if (property_type == `OVL_ASSERT) begin
              A_OVL_ARBITER_GNT_IN_WINDOW_P:
              assert property (OVL_ARBITER_GNT_IN_WINDOW_P)
              else begin
                ovl_error_t(`OVL_FIRE_2STATE,"Grant was not issued within the specified time window");
                error_event = 1;
              end
            end
            else begin
              M_OVL_ARBITER_GNT_IN_WINDOW_P:
              assume property (OVL_ARBITER_GNT_IN_WINDOW_P);
            end

          end : min_e_0_max_g_0

          if(( max_cks==0) && (min_cks>0)) begin : min_g_0_max_e_0

          // when max_cks == 0

            property OVL_ARBITER_GNT_IN_WINDOW_P;
              @(posedge clk)
                disable iff(`OVL_RESET_SIGNAL != 1'b1)
                  (((!reqs[i])|| gnts[i]) ##1
                       reqs[i]) |->
                            ((!gnts[i])[*min_cks]);
            endproperty

            if (property_type == `OVL_ASSERT) begin : property_type_ovl_assert_1
              A_OVL_ARBITER_GNT_IN_WINDOW_P:
              assert property (OVL_ARBITER_GNT_IN_WINDOW_P)
              else begin
                ovl_error_t(`OVL_FIRE_2STATE,"Grant was not issued within the specified time window");
                error_event = 1;
              end
            end : property_type_ovl_assert_1
            else begin
              M_OVL_ARBITER_GNT_IN_WINDOW_P:
              assume property (OVL_ARBITER_GNT_IN_WINDOW_P);
            end

          end : min_g_0_max_e_0

          if ((max_cks == 0) && (min_cks == 0)  // no check
               || (min_cks * max_cks < 0)) begin : min_e_0_max_e_0
            property OVL_ARBITER_GNT_IN_WINDOW_P;
              @(posedge clk)
                disable iff(`OVL_RESET_SIGNAL != 1'b1)
                  (((!reqs[i])|| gnts[i]) ##1
                       reqs[i]) |->
                         gnts[i];
            endproperty

            if (property_type == `OVL_ASSERT) begin
              A_OVL_ARBITER_GNT_IN_WINDOW_P:
              assert property (OVL_ARBITER_GNT_IN_WINDOW_P)
              else begin
                ovl_error_t(`OVL_FIRE_2STATE,"Grant was not issued within the specified time window");
                error_event = 1;
              end
            end
            else begin
              M_OVL_ARBITER_GNT_IN_WINDOW_P:
              assume property (OVL_ARBITER_GNT_IN_WINDOW_P);
            end

          end : min_e_0_max_e_0

          // granted only if requested
          // assumes that reqs stay asserted until
          // granted unless cancelled

          property OVL_ARBITER_ONE_CYCLE_GRANT_P;
            @(posedge clk)
              disable iff (`OVL_RESET_SIGNAL != 1'b1)
                past_reqs[i] && past_gnts[i] |->
                  !gnts[i] ||
                    ( reqs[i] && ($countones(reqs) == 1) &&
                      (min_cks == 0));
          endproperty

          if (property_type == `OVL_ASSERT) begin : property_type_ovl_assert_2
            A_OVL_ARBITER_ONE_CYCLE_GRANT_P:
            assert property (OVL_ARBITER_ONE_CYCLE_GRANT_P)
            else begin
              ovl_error_t(`OVL_FIRE_2STATE,"Grant was asserted for longer than 1 cycle");
              error_event = 1;
            end
          end : property_type_ovl_assert_2
          else begin
            M_OVL_ARBITER_ONE_CYCLE_GRANT_P:
            assume property (OVL_ARBITER_ONE_CYCLE_GRANT_P);
          end 

          property OVL_ARBITER_GNT_ONLY_IF_REQ_P;
            @(posedge clk)
              disable iff(`OVL_RESET_SIGNAL != 1'b1)
                !reqs[i] |-> !gnts[i];
          endproperty

          if (property_type == `OVL_ASSERT) begin : property_type_ovl_assert_3
            A_OVL_ARBITER_GNT_ONLY_IF_REQ_P:
            assert property (OVL_ARBITER_GNT_ONLY_IF_REQ_P)
            else begin
              ovl_error_t(`OVL_FIRE_2STATE,"Grant was issued without a request");
              error_event = 1;
            end
          end : property_type_ovl_assert_3
          else begin
            M_OVL_ARBITER_GNT_ONLY_IF_REQ_P:
            assume property (OVL_ARBITER_GNT_ONLY_IF_REQ_P);
          end 

          for (j=0; j<width; j=j+1) begin : loop_B

            // fifo check
            // detect request i holding and not yet granted and
            // another req j comes along. j should be granted after i.
            // would need an "if" to eliminate the case when i == j
            // but this is handled by a vacuous success here

            if( fifo_chk && ( i != j) ) begin : fifo_check

              sequence s_order_detect;
               @(posedge clk)
                  (reqs[i] && (`OVL_RESET_SIGNAL != 1'b0) && !gnts[i]) throughout
                    ($rose(reqs[i]) ||
                     (reqs[i] && $past(reqs[i] && gnts[i]))) ##[1:$]
                    (($rose(reqs[j]) ||
                     (reqs[j] && $past(reqs[j] && gnts[j]))) &&
                     (!priority_check ||
                     (priorities[priority_width*(i+1)-1 : priority_width*i] ==
                       priorities[priority_width*(j+1)-1 : priority_width*j])));
              endsequence

              property OVL_ARBITER_FIFO_P;
                @(posedge clk)
                  disable iff(`OVL_RESET_SIGNAL != 1'b1)
                    (s_order_detect.ended) |->
                       !gnts[j] throughout ##[0:$]
                          (gnts[i] || // OK
                           !reqs[i]); // req i cancelled

              endproperty

              if (property_type == `OVL_ASSERT) begin
                A_OVL_ARBITER_FIFO_P:
                assert property (OVL_ARBITER_FIFO_P)
                else begin
                  ovl_error_t(`OVL_FIRE_2STATE,"Grant was issued for a request that was not the longest pending request");
                  error_event = 1;
                end
              end
              else begin
                M_OVL_ARBITER_FIFO_P:
                assume property (OVL_ARBITER_FIFO_P);
              end

            end : fifo_check

            if( fairness_chk && (i!=j) ) begin  : fairness_check

              // fairness check
              // forbid requests i and j active at the same
              // priorities and i is granted twice

              sequence s_two_active_trig;
                @(posedge clk)
                  (
                  reqs[j] && reqs[i] && (`OVL_RESET_SIGNAL != 1'b0) && !gnts[j] &&
                    (!priority_check ||
                    (priorities[priority_width*(i+1)-1 : priority_width*i] ==
                      priorities[priority_width*(j+1)-1 : priority_width*j]))
                  ) throughout
                     ((!gnts[i])[*min_cks] ##1 gnts[i]);
              endsequence

              property OVL_ARBITER_FAIRNESS_P;
                @(posedge clk)
                  disable iff(`OVL_RESET_SIGNAL != 1'b1)
                    s_two_active_trig.ended |->
                      ##1 ((!gnts[i])[*0:$]) ##1 (gnts[j] ||
                                                   !reqs[j]);
              endproperty

              if (property_type == `OVL_ASSERT) begin
                A_OVL_ARBITER_FAIRNESS_P:
                assert property (OVL_ARBITER_FAIRNESS_P)
                else begin
                  ovl_error_t(`OVL_FIRE_2STATE,"Two grants were issued to the same channel while another channel's request was pending");
                  error_event = 1;
                end
              end
              else begin
                M_OVL_ARBITER_FAIRNESS_P:
                assume property (OVL_ARBITER_FAIRNESS_P);
              end

            end : fairness_check

          end : loop_B

        end : loop_A

        if( lru_chk) begin : lru_check

          for (j=0; j<width; j=j+1) begin : incorrect_grant
            property OVL_ARBITER_LRU_P;
               @(posedge clk)
                  disable iff(`OVL_RESET_SIGNAL != 1'b1)
                     gnts[j] && reqs[j] |->
                        predicted_gnts[j];
            endproperty

            if (property_type == `OVL_ASSERT) begin
              A_OVL_ARBITER_LRU_P:
              assert property (OVL_ARBITER_LRU_P)
              else begin
                ovl_error_t(`OVL_FIRE_2STATE,"Grant was issued to a channel that was more-recently used than another channel with a pending request");
                error_event = 1;
              end
            end
            else begin
              M_OVL_ARBITER_LRU_P:
              assume property (OVL_ARBITER_LRU_P);
            end

          end : incorrect_grant

        end : lru_check

// ensure mutual exclusion on gnts

        if( one_cycle_gnt_check) begin : one_cycle_gnt_chk
          property OVL_ARBITER_SINGLE_GRANT_P;
            @(posedge clk)
              disable iff(`OVL_RESET_SIGNAL != 1'b1)
            $countones(gnts) <= 1;
          endproperty

          if (property_type == `OVL_ASSERT) begin
            A_OVL_ARBITER_SINGLE_GRANT_P:
            assert property (OVL_ARBITER_SINGLE_GRANT_P)
            else begin
              ovl_error_t(`OVL_FIRE_2STATE,"Multiple grants were issued in the same clock cycle");
              error_event = 1;
            end
          end
          else begin
            M_OVL_ARBITER_SINGLE_GRANT_P:
            assume property (OVL_ARBITER_SINGLE_GRANT_P);
          end

        end : one_cycle_gnt_chk

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else

    if (property_type == `OVL_ASSERT) begin : property_type_ovl_assert_4
      A_OVL_ARBITER_XZ_ON_REQS_P:
      assert property (OVL_ARBITER_XZ_ON_REQS_P)
      else begin
        ovl_error_t(`OVL_FIRE_XCHECK,"reqs contains X or Z");
        error_event_xz = 1;
      end

      A_OVL_ARBITER_XZ_ON_GNTS_P:
      assert property (OVL_ARBITER_XZ_ON_GNTS_P)
      else begin
        ovl_error_t(`OVL_FIRE_XCHECK,"gnts contains X or Z");
        error_event_xz = 1;
      end 

      if (priority_check) begin : priorities_xz
        A_OVL_ARBITER_XZ_ON_PRIORITIES_P:
        assert property (OVL_ARBITER_XZ_ON_PRIORITIES_P)
        else begin
          ovl_error_t(`OVL_FIRE_XCHECK,"priorities contains X or Z");
          error_event_xz = 1;
        end
      end : priorities_xz
    end : property_type_ovl_assert_4
    else begin

      M_OVL_ARBITER_XZ_ON_REQS_P:
      assume property (OVL_ARBITER_XZ_ON_REQS_P);

      M_OVL_ARBITER_XZ_ON_GNTS_P:
      assume property (OVL_ARBITER_XZ_ON_GNTS_P);

      if (priority_check) begin : priorities_xz
        M_OVL_ARBITER_XZ_ON_PRIORITIES_P:
        assume property (OVL_ARBITER_XZ_ON_PRIORITIES_P);
      end : priorities_xz

    end

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

  covergroup latency_cg(ref logic cov_gnt, ref integer cov_cnt)
    @(posedge clk);
    cv1 : coverpoint cov_cnt
      iff ( ( gnts != 0) &&
              (`OVL_RESET_SIGNAL != 1'b0) &&
            ( cov_gnt && ( cov_cnt>=0))) {
        bins time_to_grant_good[] = {[min_cks:max_cks]};
        bins time_to_grant_bad = default;
      }
      option.per_instance = 1;
      option.at_least = 1;
      option.name = "time_to_grant";
      option.comment = "Bin index is the observed latency in clock cycles";
  endgroup : latency_cg

  covergroup reqs_cg(ref integer no_reqs) @(posedge clk);
    cv2 : coverpoint no_reqs
      iff ( (`OVL_RESET_SIGNAL != 1'b0) &&
            ( |gnts)) {
        bins observed_reqs_good[] = {[1:width]};
      }
      option.per_instance = 1;
      option.at_least = 1;
      option.name = "concurrent_requests";
      option.comment =
      "Bin index is the number of observed concurrent requests";
  endgroup : reqs_cg

`endif  // `ifdef OVL_COVERGROUP_ON

  generate

    if (coverage_level != `OVL_COVER_NONE) begin : ovl_cover

      if (OVL_COVER_SANITY_ON) begin : ovl_cover_sanity

      end : ovl_cover_sanity

      if (OVL_COVER_BASIC_ON) begin : ovl_cover_basic

        for( i = 0; i< width; i=i+1) begin : loop_A

          // a non-cancelled req is eventually granted
          // within allowed latency

          if ((max_cks > 0) && (min_cks > 0)) begin : min_g_0_max_g_0

            cover_req_granted :
              cover property( @ (posedge clk)
                (`OVL_RESET_SIGNAL != 1'b0) throughout
                ( ( ( (!reqs[i])|| gnts[i]) ##1
                  reqs[i]) ##0
                     ((!gnts[i]) && reqs[i])[*min_cks:max_cks]
                       ##1 (gnts[i])))
            ovl_cover_t ("request is granted within specified time window");

          end : min_g_0_max_g_0

          if ((max_cks > 0) && (min_cks == 0)) begin : min_e_0_max_g_0

            cover_req_granted :
              cover property( @ (posedge clk)
                (`OVL_RESET_SIGNAL != 1'b0) throughout (
                  ( ( (!reqs[i])|| gnts[i]) ##1
                    reqs[i]) ##0
                      ((!gnts[i]) && reqs[i])[*0:max_cks] ##1
                        (gnts[i])))
            ovl_cover_t ("request is granted within specified time window");

          end : min_e_0_max_g_0

          if(( max_cks==0) && (min_cks>0)) begin : min_g_0_max_e_0

          // when max_cks == 0

            cover_req_granted :
              cover property( @ (posedge clk)
                (`OVL_RESET_SIGNAL != 1'b0) throughout(
                  ( ( (!reqs[i])|| gnts[i]) ##1
                    reqs[i]) ##0
                       ( (!gnts[i]) && reqs[i])[*min_cks:$] ##1
                         ( gnts[i])))
            ovl_cover_t ("request is granted within specified time window");

          end : min_g_0_max_e_0

          if ((max_cks == 0) && (min_cks == 0)  // no check
               || (min_cks * max_cks < 0)) begin : min_e_0_max_e_0

            cover_req_granted :
              cover property( @ (posedge clk)
                 (`OVL_RESET_SIGNAL != 1'b0) throughout(
                   ( (!reqs[i])|| gnts[i]) ##1
                      reqs[i] ##0 gnts[i]))
            ovl_cover_t ("request is granted within specified time window");

          end : min_e_0_max_e_0

          cover_req_aborted :
            cover property( @ (posedge clk)
          ( (`OVL_RESET_SIGNAL != 1'b0) &&
          $fell( reqs[i]) && !( past_gnts[i])))
          ovl_cover_t ("request is aborted before grant");

        end : loop_A

      end : ovl_cover_basic

      if (OVL_COVER_STATISTIC_ON) begin : ovl_cover_statistic

`ifdef OVL_COVERGROUP_ON

        for( gen_chnl = 0; gen_chnl < width; gen_chnl++) begin : chnl

          integer cnt;

          always @ (posedge clk) begin
            if((`OVL_RESET_SIGNAL != 1'b1) || !reqs[gen_chnl]) begin
              cnt <= -1;
              // -1 makes sure that subBIN[0] is not updated.
            end
            else if (((!past_reqs[gen_chnl]) || past_gnts[gen_chnl]) &&
                     reqs[gen_chnl]) begin
              cnt <= 1;
            end
            else begin
              cnt <= cnt+1;
            end
          end

          integer delay_cnt;
          reg     cov_grant;

          always @ (*) begin
            delay_cnt = ( (((!past_reqs[gen_chnl]) || past_gnts[gen_chnl]) && reqs[gen_chnl])
                                 ? 0
                                 : cnt);
            cov_grant = gnts[gen_chnl];
          end

          latency_cg latency_cover = new(cov_grant, delay_cnt);

        end : chnl

        integer cov_nb_of_reqs;

        always @ (*) begin
          cov_nb_of_reqs = $countones( reqs);
        end

        reqs_cg reqs_cover = new( cov_nb_of_reqs);

`endif  // `ifdef OVL_COVERGROUP_ON

      end : ovl_cover_statistic

      if (OVL_COVER_CORNER_ON) begin : ovl_cover_corner

        for( i = 0; i< width; i=i+1) begin : loop_A

          cover_req_granted_at_min_cks:
            cover property (
              @(posedge clk)
                (`OVL_RESET_SIGNAL != 1'b0) throughout(
                  ( (!reqs[i])|| gnts[i]) ##1
                    reqs[i] ##0
                      ( (!gnts[i]) [*min_cks]
                         ##1 gnts[i])))
            ovl_cover_t ("grant issued min_cks cycles after request");

          if( max_cks > 0 || ( max_cks == 0 && min_cks ==0)) begin : gnt_ex_at_max
            cover_req_granted_at_max_cks:
              cover property (
                @(posedge clk)
                  (`OVL_RESET_SIGNAL != 1'b0) throughout(
                    ( (!reqs[i])|| gnts[i]) ##1
                       reqs[i] ##0
                          ( (!gnts[i]) [*max_cks]
                               ##1 gnts[i])))
            ovl_cover_t ("grant issued max_cks cycles after request");
          end : gnt_ex_at_max

        end : loop_A

      end : ovl_cover_corner

    end : ovl_cover

  endgenerate

`endif // OVL_COVER_ON

