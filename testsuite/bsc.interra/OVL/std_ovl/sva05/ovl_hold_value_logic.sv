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

  reg               sva_checker_time_0 = 1'b1;

  always @ (posedge clk) begin
    if(`OVL_RESET_SIGNAL != 1'b1)
      sva_checker_time_0  <= 1'b1;
    else
      sva_checker_time_0  <= 1'b0;
  end

`ifdef OVL_SYNTHESIS
`else
  generate
    if (max < 0) begin : max_l_0
          initial $display("Illegal max parameter value < 0");
    end : max_l_0
    if ((max !=0) && (max < min)) begin : max_ne_0_max_l_min
      initial $display("Illegal max parameter value < min");
    end : max_ne_0_max_l_min
    if (min < 0) begin : min_l_0
      initial $display("Illegal min parameter value < 0");
    end : min_l_0
  endgenerate
`endif

`endif // OVL_SHARED_CODE

`ifdef OVL_ASSERT_ON

// Properties for the below 4 cases and XZ checking:
//   case1 -> min = 0, max = 0
//   case2 -> min = 0, max > 0
//   case3 -> min > 0, min <= max
//   case4 -> min > 0, max = 0
//   XZ checking on test_expr
//   XZ checking on value input

  property OVL_HOLD_VALUE_CASE1_P;
    @(posedge clk)
      disable iff(`OVL_RESET_SIGNAL != 1'b1)
        ( ( !$stable( test_expr) || sva_checker_time_0) &&
           ( test_expr == value)) |=>
             ( !$stable( test_expr));
  endproperty

  property OVL_HOLD_VALUE_CASE2_P;
    @(posedge clk)
      disable iff(`OVL_RESET_SIGNAL != 1'b1)
        ( ( !$stable( test_expr) || sva_checker_time_0) &&
           ( test_expr == value)) |=>
          ( ( !$stable( test_expr)) or
            ( ( test_expr == value)[*1:(max > 0 ? max : 1)] ##1 (!$stable( test_expr))));
  endproperty

  property OVL_HOLD_VALUE_CASE3_P;
    @(posedge clk)
      disable iff(`OVL_RESET_SIGNAL != 1'b1)
        ( ( !$stable( test_expr) || sva_checker_time_0) &&
           ( test_expr == value)) |=>
          ( ( test_expr == value)[*min:(max >= min ? max : min)] ##1 (!$stable( test_expr)));
  endproperty

  property OVL_HOLD_VALUE_CASE4_P;
    @(posedge clk)
      disable iff(`OVL_RESET_SIGNAL != 1'b1)
        ( ( !$stable( test_expr) || sva_checker_time_0) &&
           ( test_expr == value)) |=>
          ( ( test_expr == value)[*min:$] ##1 !$stable( test_expr));
  endproperty


`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else

    property OVL_HOLD_VALUE_XZ_ON_TEST_EXPR_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    (!($isunknown(test_expr)));
    endproperty

    property OVL_HOLD_VALUE_XZ_ON_VALUE_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    (!($isunknown(value)));
    endproperty

  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

  generate
    case (property_type)
      `OVL_ASSERT_2STATE,
      `OVL_ASSERT: begin : ovl_assert

        if(( min == 0) && ( max == 0)) begin : min_e_0_max_e_0
          A_OVL_HOLD_VALUE_CASE1_P:
          assert property (OVL_HOLD_VALUE_CASE1_P)
          else begin
            ovl_error_t(`OVL_FIRE_2STATE,"A match occurred and the expression had the same value in the next cycle");
            error_event = 1;
          end
        end : min_e_0_max_e_0

        if((min == 0) && ( max > 0)) begin : min_e_0_max_g_0
          A_OVL_HOLD_VALUE_CASE2_P:
          assert property (OVL_HOLD_VALUE_CASE2_P)
          else begin
            ovl_error_t(`OVL_FIRE_2STATE,"A match occurred and the expression held the same value for the next `max' cycles");
            error_event = 1;
          end
        end : min_e_0_max_g_0

        if (( min > 0) && ( min <= max)) begin : min_g_0_min_le_max
          A_OVL_HOLD_VALUE_CASE3_P:
          assert property (OVL_HOLD_VALUE_CASE3_P)
          else begin
            ovl_error_t(`OVL_FIRE_2STATE,"A match occurred and the expression changed value before the event window or held the same value through the event window");
            error_event = 1;
          end
        end : min_g_0_min_le_max

        if(( min > 0) && ( max == 0)) begin : min_g_0_max_e_0
          A_OVL_HOLD_VALUE_CASE4_P:
          assert property (OVL_HOLD_VALUE_CASE4_P)
          else begin
            ovl_error_t(`OVL_FIRE_2STATE,"A match occurred and the expression changed value before the event window opened");
            error_event = 1;
          end
        end : min_g_0_max_e_0

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else

        A_OVL_HOLD_VALUE_XZ_ON_TEST_EXPR_P:
        assert property (OVL_HOLD_VALUE_XZ_ON_TEST_EXPR_P)
        else begin
          ovl_error_t(`OVL_FIRE_XCHECK,"test_expr contains X or Z");
          error_event_xz = 1;
        end

        A_OVL_HOLD_VALUE_XZ_ON_VALUE_P:
        assert property (OVL_HOLD_VALUE_XZ_ON_VALUE_P)
        else begin
          ovl_error_t(`OVL_FIRE_XCHECK,"value contains X or Z");
          error_event_xz = 1;
        end

  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

      end

      `OVL_ASSUME_2STATE,
      `OVL_ASSUME: begin : ovl_assume

        if(( min == 0) && ( max == 0)) begin : min_e_0_max_e_0
          M_OVL_HOLD_VALUE_CASE1_P:
          assume property (OVL_HOLD_VALUE_CASE1_P);
        end : min_e_0_max_e_0

        if((min == 0) && ( max > 0)) begin : min_e_0_max_g_0
          M_OVL_HOLD_VALUE_CASE2_P:
          assume property (OVL_HOLD_VALUE_CASE2_P);
        end : min_e_0_max_g_0

        if (( min > 0) && ( min <= max)) begin : min_g_0_min_le_max
          M_OVL_HOLD_VALUE_CASE3_P:
          assume property (OVL_HOLD_VALUE_CASE3_P);
        end : min_g_0_min_le_max

        if(( min > 0) && ( max == 0)) begin : min_g_0_max_e_0
          M_OVL_HOLD_VALUE_CASE4_P:
          assume property (OVL_HOLD_VALUE_CASE4_P);
        end : min_g_0_max_e_0

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else

        M_OVL_HOLD_VALUE_XZ_ON_TEST_EXPR_P:
        assume property (OVL_HOLD_VALUE_XZ_ON_TEST_EXPR_P);

        M_OVL_HOLD_VALUE_XZ_ON_VALUE_P:
        assume property (OVL_HOLD_VALUE_XZ_ON_VALUE_P);

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

  wire changed_exp;

  reg               past_not_resetting = 1'b0;
  reg [width-1 : 0] past_exp           = {width{1'b0}};
  reg [width-1 : 0] past_value         = {width{1'b0}};

  assign changed_exp = ( test_expr != past_exp);

  always @ (posedge clk) begin
    past_not_resetting <= (`OVL_RESET_SIGNAL != 1'b0);
    if(`OVL_RESET_SIGNAL != 1'b1) begin
      past_exp            <= {width{1'b0}};
      past_value          <= {width{1'b0}};
    end
    else begin
      past_exp            <= test_expr;
      past_value          <= value;
    end
  end

  integer cnt = 0;

  localparam d_max = (max > 0) ? (max + 1) : ((min > 0) ? (min + 4095) : 1);

  always @(posedge clk) begin
    if(`OVL_RESET_SIGNAL != 1'b1) begin
      cnt <= 0;
    end    
    else if( changed_exp | !past_not_resetting) begin
      if( test_expr == value)
        cnt <= 1;
      else
        cnt <= 0;
    end
    else if( ( test_expr == value) && ( cnt > 0)) begin
        cnt <= cnt + 1;
    end
  end

  covergroup hold_time_cg @(posedge clk);
    coverpoint cnt
      iff((`OVL_RESET_SIGNAL != 1'b0) &&
        past_not_resetting &&
          (past_exp == past_value) && ( cnt > 0)) {
             bins observed_hold_time_good[] = {[min+1:d_max]};
             bins observed_hold_time_bad = default;
       }
    option.per_instance = 1;
    option.at_least = 1;
    option.name = "observed_hold_time";
    option.comment = "Bin index is the observed hold time";
  endgroup :hold_time_cg

`endif  //  `ifdef OVL_COVERGROUP_ON

  generate

    if (coverage_level != `OVL_COVER_NONE) begin : ovl_cover

      if (OVL_COVER_SANITY_ON) begin : ovl_cover_sanity

        cover_test_expr_changes :
           cover property(
              @(posedge clk)
                (`OVL_RESET_SIGNAL != 1'b0) &&
             !$stable(test_expr))
             ovl_cover_t("Test expression changed value");

      end : ovl_cover_sanity

      if (OVL_COVER_BASIC_ON) begin : ovl_cover_basic

      end : ovl_cover_basic

      if (OVL_COVER_STATISTIC_ON) begin : ovl_cover_statistic

`ifdef OVL_COVERGROUP_ON
        hold_time_cg cover_observed_hold_time = new();
`endif

      end : ovl_cover_statistic

      if (OVL_COVER_CORNER_ON) begin : ovl_cover_corner

        cover_hold_value_for_min_cks :
          cover property(
            @(posedge clk)
              (`OVL_RESET_SIGNAL != 1'b0) throughout(
                ( ( !$stable( test_expr) || sva_checker_time_0) &&
              ( test_expr == value)) ##0
                    ( ( ( test_expr==value)[*min]) ##1
                      ( !$stable( test_expr)))))
          ovl_cover_t("Test expr was stable at value for exactly min clock cycles");

    if (!(( min > 0) && ( max == 0))) begin
        cover_hold_value_for_max_cks :
          cover property(
            @(posedge clk)
              (`OVL_RESET_SIGNAL != 1'b0) throughout(
                ( ( !$stable( test_expr) || sva_checker_time_0) &&
              ( test_expr == value)) ##0
                    ( ( ( test_expr==value)[*max]) ##1
                      ( !$stable( test_expr)))))
          ovl_cover_t("Test expr was stable at value for exactly max clock cycles");
    end

      end : ovl_cover_corner

    end : ovl_cover

  endgenerate

`endif // OVL_COVER_ON
