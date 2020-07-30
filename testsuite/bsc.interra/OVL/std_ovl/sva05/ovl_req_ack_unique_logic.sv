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

  localparam max_cks_log_2 = log2(max_cks);

  wire                   full;
  wire                   empty;

  genvar                 i;

`endif  //  OVL_SHARED_CODE

  generate

`ifdef OVL_ASSERT_ON

    if( method == 0) begin : method_0
      reg [max_cks_log_2:0] req_id;
      reg [max_cks_log_2:0] ack_id;

`ifdef OVL_SYNTHESIS
`else
      initial begin
         req_id = 'b0;
         ack_id = 'b0;
      end
`endif

      assign full =
        (req_id >= ack_id ? ((req_id - ack_id) == max_cks) :
            (((2*max_cks) - ack_id + req_id) == max_cks)) &&
              req && !ack && (`OVL_RESET_SIGNAL != 1'b0);

      assign empty =
        ((`OVL_RESET_SIGNAL != 1'b0) && (req_id == ack_id) && ack &&
            (!req || (min_cks>0)));

      always @ (posedge clk) begin

        req_id <= (`OVL_RESET_SIGNAL != 1'b1) ? 0 :
          req && !full &&
          (req_id[max_cks_log_2:0]==2*max_cks-1) ? 0 :
            req && !full ?
              req_id+{{(max_cks_log_2){1'b0}},  1'b1} :
                req_id;

        ack_id <= (`OVL_RESET_SIGNAL != 1'b1) ? 0 :
          ack && !empty &&
          (ack_id[max_cks_log_2:0]==2*max_cks-1) ? 0 :
            ack && !empty ?
              ack_id+{{(max_cks_log_2){1'b0}},  1'b1} :
                ack_id;
      end

      property OVL_REQ_ACK_UNIQUE_EXTRANEOUS_ACK_P;
        @(posedge clk) not empty;
      endproperty

      property OVL_REQ_ACK_UNIQUE_MAX_OUTSTANDING_REQ_P;
        @(posedge clk) not full;
      endproperty

      case (property_type)
        `OVL_ASSERT, `OVL_ASSUME : begin : ovl_assert_assume

          if (property_type == `OVL_ASSERT) begin : property_type_ovl_assert_1

            A_OVL_REQ_ACK_UNIQUE_EXTRANEOUS_ACK_P:
            assert property (OVL_REQ_ACK_UNIQUE_EXTRANEOUS_ACK_P)
            else begin
              ovl_error_t(`OVL_FIRE_2STATE,"ack received without any outstanding req");
              error_event = 1;
            end

            A_OVL_REQ_ACK_UNIQUE_MAX_OUTSTANDING_REQ_P:
            assert property (OVL_REQ_ACK_UNIQUE_MAX_OUTSTANDING_REQ_P)
            else begin
              ovl_error_t(`OVL_FIRE_2STATE,"Number of outstanding req exceeded possible maximum number i.e. max_cks");
              error_event = 1;
            end

          end : property_type_ovl_assert_1
          else begin

            M_OVL_REQ_ACK_UNIQUE_EXTRANEOUS_ACK_P:
            assume property (OVL_REQ_ACK_UNIQUE_EXTRANEOUS_ACK_P);

            M_OVL_REQ_ACK_UNIQUE_MAX_OUTSTANDING_REQ_P:
            assume property (OVL_REQ_ACK_UNIQUE_MAX_OUTSTANDING_REQ_P);

          end

          if( (min_cks <= max_cks)) begin :min_l_e_max

            for (i=0; i<2*max_cks; i=i+1) begin : loop_0
              property OVL_REQ_ACK_UNIQUE_ACK_TIMEOUT_P;
                @(posedge clk)
                  disable iff( `OVL_RESET_SIGNAL != 1'b1)
                    ( req && req_id==i) && !full |->
                      ##[min_cks:max_cks]((ack_id==i) && ack);
              endproperty

              if (property_type == `OVL_ASSERT) begin : property_type_ovl_assert_2
                A_OVL_REQ_ACK_UNIQUE_ACK_TIMEOUT_P:
                assert property (OVL_REQ_ACK_UNIQUE_ACK_TIMEOUT_P)
                else begin
                  ovl_error_t(`OVL_FIRE_2STATE,"ack not received within min to max time");
                  error_event = 1;
                end
              end : property_type_ovl_assert_2
              else begin
                M_OVL_REQ_ACK_UNIQUE_ACK_TIMEOUT_P:
                assume property (OVL_REQ_ACK_UNIQUE_ACK_TIMEOUT_P);
              end

            end : loop_0

          end : min_l_e_max

          if((min_cks > max_cks) && (max_cks == 0)) begin : min_g_max_max_e_0

            for (i=0; i<2*min_cks; i=i+1) begin : loop_1
              property OVL_REQ_ACK_UNIQUE_ACK_TIMEOUT_P;
                @(posedge clk)
                  disable iff( `OVL_RESET_SIGNAL != 1'b1)
                  ( req && req_id==i) && !full |->
                      ##[min_cks:$]((ack_id==i) && ack);
              endproperty

              if (property_type == `OVL_ASSERT) begin
                A_OVL_REQ_ACK_UNIQUE_ACK_TIMEOUT_P:
                assert property (OVL_REQ_ACK_UNIQUE_ACK_TIMEOUT_P)
                else begin
                  ovl_error_t(`OVL_FIRE_2STATE,"ack not received within min to max time");
                  error_event = 1;
                end
              end
              else begin
                M_OVL_REQ_ACK_UNIQUE_ACK_TIMEOUT_P:
                assume property (OVL_REQ_ACK_UNIQUE_ACK_TIMEOUT_P);
              end

            end : loop_1
          end : min_g_max_max_e_0

        end : ovl_assert_assume

        `OVL_IGNORE : begin : ovl_ignore
          // do nothing;
        end

        default     : initial ovl_error_t(`OVL_FIRE_2STATE,"");

      endcase

    end : method_0

`endif // OVL_ASSERT_ON

    if (method == 1) begin : method_1

`ifdef OVL_SHARED_CODE

      reg  [31:0]                clock_count;
      reg  [max_cks_log_2-1 : 0] head;
      reg  [max_cks_log_2-1 : 0] tail;
      reg  [31:0]                queue [0:max_cks];
      reg  [max_cks_log_2-1 : 0] outstanding_req;
      reg  [max_cks_log_2-1 : 0] past_outstanding_req;
      wire [31:0]                delay;

      function [31:0] latency
        (
         input [31:0] current,
         input [31:0] previous
         );
        latency = (current - previous);
      endfunction

      assign delay = latency(clock_count,queue[head]);
      assign full  = (outstanding_req == max_cks);
      assign empty = (outstanding_req == 0);

      always @(posedge clk) begin
        past_outstanding_req <= outstanding_req;

        clock_count <= (`OVL_RESET_SIGNAL != 1'b1) ? 0
                                                   : (clock_count + 1);

        queue[tail] <= req ? clock_count : queue[tail];

        head <= (`OVL_RESET_SIGNAL != 1'b1) ? 0 :
          (ack && !empty ?
            ((head == max_cks) ? 0 :
              head + {{(max_cks_log_2-1){1'b0}},1'b1}) :
             head);

        tail <= (`OVL_RESET_SIGNAL != 1'b1) ? 0 :
          (req ?
            ((empty && ack &&
             (min_cks ==0)) ? tail :
              ((!ack && full) ? tail : ((tail == max_cks) ? 0 :
                tail + {{(max_cks_log_2-1){1'b0}},1'b1}))) :
              tail);

        outstanding_req <=
          (`OVL_RESET_SIGNAL != 1'b1) ? 0:
            req ?
              (ack && (!empty || (min_cks ==0)) ?
                outstanding_req :
                (!full ?
                  outstanding_req + {{(max_cks_log_2-1){1'b0}},1'b1} :
                     outstanding_req)) :
                (ack && !empty ?
                  outstanding_req - {{(max_cks_log_2-1){1'b0}},1'b1} :
                    outstanding_req);

      end

`endif  //  OVL_SHARED_CODE

`ifdef OVL_ASSERT_ON

      property OVL_REQ_ACK_UNIQUE_MAX_OUTSTANDING_REQ_P;
        @(posedge clk) not
          (`OVL_RESET_SIGNAL != 1'b0) && req && !ack && full;
      endproperty

      property OVL_REQ_ACK_UNIQUE_EXTRANEOUS_ACK_P;
        @(posedge clk)
          disable iff( `OVL_RESET_SIGNAL != 1'b1)
            ack |-> (req || !(empty)) &&
                    (!(req &&(empty)) || (min_cks==0));
      endproperty

      property OVL_REQ_ACK_UNIQUE_ACK_TIMEOUT_P;
        @(posedge clk)
          disable iff( `OVL_RESET_SIGNAL != 1'b1)
            (empty ||  (((ack && delay >= min_cks) && (delay <= max_cks)) ||
                        (!ack && (delay < max_cks)))) &&
            (!(empty && ack && req) || (min_cks == 0));
      endproperty

      case (property_type)

        `OVL_ASSERT_2STATE,
        `OVL_ASSERT: begin : ovl_assert

          A_OVL_REQ_ACK_UNIQUE_EXTRANEOUS_ACK_P:
          assert property (OVL_REQ_ACK_UNIQUE_EXTRANEOUS_ACK_P)
          else begin
            ovl_error_t(`OVL_FIRE_2STATE,"ack received without any outstanding req");
            error_event = 1;
          end

          A_OVL_REQ_ACK_UNIQUE_MAX_OUTSTANDING_REQ_P:
          assert property (OVL_REQ_ACK_UNIQUE_MAX_OUTSTANDING_REQ_P)
          else begin
            ovl_error_t(`OVL_FIRE_2STATE,"Number of outstanding req exceeded possible maximum number i.e. max_cks");
            error_event = 1;
          end

          A_OVL_REQ_ACK_UNIQUE_ACK_TIMEOUT_P:
          assert property (OVL_REQ_ACK_UNIQUE_ACK_TIMEOUT_P)
          else begin
            ovl_error_t(`OVL_FIRE_2STATE,"ack not received within min to max time");
            error_event = 1;
          end

        end : ovl_assert

        `OVL_ASSUME_2STATE,
        `OVL_ASSUME: begin : ovl_assume

          M_OVL_REQ_ACK_UNIQUE_EXTRANEOUS_ACK_P:
          assume property (OVL_REQ_ACK_UNIQUE_EXTRANEOUS_ACK_P);

          M_OVL_REQ_ACK_UNIQUE_MAX_OUTSTANDING_REQ_P:
          assume property (OVL_REQ_ACK_UNIQUE_MAX_OUTSTANDING_REQ_P);

          M_OVL_REQ_ACK_UNIQUE_ACK_TIMEOUT_P:
          assume property (OVL_REQ_ACK_UNIQUE_ACK_TIMEOUT_P);

        end : ovl_assume

        `OVL_IGNORE : begin : ovl_ignore
          // do nothing;
        end

        default     : initial ovl_error_t(`OVL_FIRE_2STATE,"");

      endcase

`endif // OVL_ASSERT_ON

`ifdef OVL_COVER_ON

`ifdef OVL_COVERGROUP_ON

// latency_cg

  covergroup latency_cg( ref logic f_empty,
                         ref int f_delay ) @(posedge clk);
    c1 : coverpoint f_delay
           iff( (`OVL_RESET_SIGNAL != 1'b0) && ack &&
             ( (!f_empty) || (req && f_empty))) {
                bins observed_latency_good[] = {[min_cks:max_cks]};
                bins observed_latency_bad = default;
           }
      option.per_instance = 1;
      option.at_least = 1;
      option.name = "observed_latency";
      option.comment = "Bin index is the observed latency";
  endgroup : latency_cg

// outstanding_req_cg

  covergroup outstanding_req_cg(
          ref int f_outstanding_req,
          ref int f_past_outstanding_req) @(posedge clk);
    c2 : coverpoint f_outstanding_req
           iff( (`OVL_RESET_SIGNAL != 1'b0) &&
              (( f_outstanding_req != f_past_outstanding_req) ||
              (!(|f_outstanding_req)))) {
              bins observed_outstanding_req[] = {[0:max_cks]};
         }
    option.per_instance = 1;
    option.at_least = 1;
    option.name = "observed_outstanding_requests";
    option.comment = "Bin index is the number of outstanding requests";
  endgroup : outstanding_req_cg

`endif  // `ifdef OVL_COVERGROUP_ON

  if (coverage_level != `OVL_COVER_NONE) begin

    if (OVL_COVER_STATISTIC_ON) begin : ovl_cover_statistic

`ifdef OVL_COVERGROUP_ON

      int cov_delay;
      reg cov_empty;
      always @(*) begin
         cov_delay = int'( !empty ? delay : 0);
         cov_empty = empty;
      end

      latency_cg cover_observed_latency = new(cov_empty, cov_delay);

      int cov_outstanding_req;
      int cov_past_outstanding_req;
      always @(*) begin
        cov_outstanding_req = int'( outstanding_req);
        cov_past_outstanding_req = int'( past_outstanding_req);
      end

      outstanding_req_cg cover_outstanding_requests = new(cov_outstanding_req, cov_past_outstanding_req);

`endif  // `ifdef OVL_COVERGROUP_ON

    end : ovl_cover_statistic

    if (OVL_COVER_CORNER_ON) begin : ovl_cover_corner

      cover_ack_with_exact_min_lat:
        cover property( @(posedge clk)
            ((`OVL_RESET_SIGNAL != 1'b0) && ack &&
           (empty ? (min_cks == 0) && req : (delay == min_cks))
          ))
      ovl_cover_t("Observed latency is exactly equal to specified min value");

      cover_ack_with_exact_max_lat:
        cover property( @(posedge clk)
            ((`OVL_RESET_SIGNAL != 1'b0) && ack &&
             (empty ? ((max_cks == 0) && (min_cks == 0) && req)
                       : (delay == max_cks))
             ))
      ovl_cover_t("Observed latency is exactly equal to specified max value");

    end : ovl_cover_corner

  end

`endif  //  OVL_COVER_ON

    end : method_1

`ifdef OVL_COVER_ON

    if (coverage_level != `OVL_COVER_NONE) begin : ovl_cover_on

      if (OVL_COVER_SANITY_ON) begin : ovl_cover_sanity

        cover_number_of_req :
          cover property ( @(posedge clk)
              (`OVL_RESET_SIGNAL != 1'b0) && req)
        ovl_cover_t("req input asserted");

        cover_number_of_ack :
          cover property ( @(posedge clk)
              (`OVL_RESET_SIGNAL != 1'b0) && ack)
        ovl_cover_t("ack input asserted");

      end : ovl_cover_sanity

    end

`endif  //  OVL_COVER_ON

  endgenerate

`ifdef OVL_ASSERT_ON

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else

    property OVL_REQ_ACK_UNIQUE_XZ_ON_REQ_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    (!($isunknown(req)));
    endproperty

    property OVL_REQ_ACK_UNIQUE_XZ_ON_ACK_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    (!($isunknown(ack)));
    endproperty

  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

  generate
    case (property_type)
      `OVL_ASSERT_2STATE,
      `OVL_ASSERT: begin : ovl_assert_xz

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else

        A_OVL_REQ_ACK_UNIQUE_XZ_ON_REQ_P:
        assert property (OVL_REQ_ACK_UNIQUE_XZ_ON_REQ_P)
        else begin
          ovl_error_t(`OVL_FIRE_XCHECK,"req contains X or Z");
          error_event_xz = 1;
        end

        A_OVL_REQ_ACK_UNIQUE_XZ_ON_ACK_P:
        assert property (OVL_REQ_ACK_UNIQUE_XZ_ON_ACK_P)
        else begin
          ovl_error_t(`OVL_FIRE_XCHECK,"ack contains X or Z");
          error_event_xz = 1;
        end

  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

      end : ovl_assert_xz

      `OVL_ASSUME_2STATE,
      `OVL_ASSUME: begin : ovl_assume_xz

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else

        M_OVL_REQ_ACK_UNIQUE_XZ_ON_REQ_P:
        assume property (OVL_REQ_ACK_UNIQUE_XZ_ON_REQ_P);

        M_OVL_REQ_ACK_UNIQUE_XZ_ON_ACK_P:
        assume property (OVL_REQ_ACK_UNIQUE_XZ_ON_ACK_P);

  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

      end : ovl_assume_xz

      `OVL_IGNORE : begin : ovl_ignore_xz
        // do nothing;
      end
      default     : initial ovl_error_t(`OVL_FIRE_2STATE,"");
    endcase
  endgenerate

`endif // OVL_ASSERT_ON

