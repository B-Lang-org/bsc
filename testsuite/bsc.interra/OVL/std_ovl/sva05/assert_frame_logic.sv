// Accellera Standard V2.8.1 Open Verification Library (OVL).
// Accellera Copyright (c) 2005-2014. All rights reserved.

`ifdef OVL_ASSERT_ON

  integer ii = 0;
  reg win = 0;
  reg r_start_event = 0;

  always @(posedge clk) begin
    r_start_event <= start_event;
  end

  always @(posedge clk) begin
    if (`OVL_RESET_SIGNAL != 1'b1) begin
      ii <= 0;
      win <= 0;
    end
    else begin
      if (max_cks > 0) begin
        case (win)
          0: begin
            if (r_start_event == 1'b0 && start_event == 1'b1 &&
                (test_expr != 1'b1)) begin
              win <= 1'b1;
              ii <= max_cks;
            end
          end
          1: begin
            if (r_start_event == 1'b0 && start_event == 1'b1 &&
                action_on_new_start == `OVL_RESET_ON_NEW_START &&
                test_expr != 1'b1) begin
              ii <= max_cks;
            end
            else if (ii <= 1 || test_expr == 1'b1) begin
              win <= 1'b0;
            end
            else begin
              ii <= ii -1;
            end
          end
        endcase
      end
      else if (min_cks > 0) begin
        case (win)
          0: begin
            if (r_start_event == 1'b0 && start_event == 1'b1 &&
                (test_expr != 1'b1)) begin
              win <= 1'b1;
              ii <= min_cks;
            end
          end
          1: begin
            if (r_start_event == 1'b0 && start_event == 1'b1 &&
                action_on_new_start == `OVL_RESET_ON_NEW_START &&
                test_expr != 1'b1) begin
              ii <= min_cks;
            end
            else if (ii <= 1 || test_expr == 1'b1) begin
              win <= 1'b0;
            end
            else begin
              ii <= ii -1;
            end
          end
        endcase
      end
    end
  end

  property ASSERT_FRAME_MIN0_MAX0_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  $rose(start_event) |-> test_expr;
  endproperty

  property ASSERT_FRAME_ERR_ON_START_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  !($rose(start_event) && win);
  endproperty

  property ASSERT_FRAME_MIN_CHECK_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  ($rose(start_event) && !win) |-> ((!test_expr[*min_cks]));
  endproperty

  property ASSERT_FRAME_MAX_CHECK_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  ($rose(start_event) && !win) |-> (!test_expr[*0:max_cks] ##1 test_expr);
  endproperty

  property ASSERT_FRAME_RESET_ON_START_MIN_CHECK_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  $rose(start_event) |-> (!test_expr ##1
                          ((!test_expr[*(min_cks > 0 ? min_cks-1 : 1)]) or
                           (!test_expr[*0:(min_cks > 0 ? min_cks-1 : 1)] ##0 $rose(start_event)))
                         );
  endproperty

  property ASSERT_FRAME_RESET_ON_START_MAX_CHECK_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  ($rose(start_event) && !test_expr) |=> (!test_expr[*0:(max_cks > 0 ? max_cks-1 : 1)] ##1
                                          (test_expr || ($rose(start_event)))
                                         );
  endproperty

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
    property ASSERT_FRAME_XZ_ON_START_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    !(win) |-> (!($isunknown(start_event)));
    endproperty

    property ASSERT_FRAME_XZ_ON_NEW_START_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    (win) |-> (!($isunknown(start_event)));
    endproperty

    property ASSERT_FRAME_XZ_ON_TEST_EXPR_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    ( ( $rose(start_event)&&(!win) ) || (win) ) |-> (!($isunknown(test_expr)));
    endproperty

    property ASSERT_FRAME_MIN_XZ_CHECK_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    ($rose(start_event) && !win) |-> (((!($isunknown(test_expr)))[*min_cks]));
    endproperty

    property ASSERT_FRAME_XZ_MIN0_MAX0_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    $rose(start_event) |-> (!($isunknown(test_expr)));
    endproperty
  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

  generate

    case (property_type)
      `OVL_ASSERT_2STATE,
      `OVL_ASSERT: begin : ovl_assert
        if (min_cks == 0 && max_cks == 0) begin : a_assert_frame_min0_max0
          A_ASSERT_FRAME_MIN0_MAX0_P:
          assert property (ASSERT_FRAME_MIN0_MAX0_P)
          else ovl_error_t(`OVL_FIRE_2STATE,"Test expression is not TRUE while start event is asserted when both parameters min_cks and max_cks are set to 0");
        end
        if (action_on_new_start == `OVL_IGNORE_NEW_START ||
            action_on_new_start == `OVL_ERROR_ON_NEW_START) begin : a_ignore_or_error_on_new_start
          if (min_cks > 0) begin : a_assert_frame_min_check
            A_ASSERT_FRAME_MIN_CHECK_P:
            assert property (ASSERT_FRAME_MIN_CHECK_P)
            else ovl_error_t(`OVL_FIRE_2STATE,"Test expression is TRUE before elapse of specified minimum min_cks cycles from start event");
          end
          if (max_cks > 0) begin : a_assert_frame_max_check
            A_ASSERT_FRAME_MAX_CHECK_P:
            assert property (ASSERT_FRAME_MAX_CHECK_P)
            else ovl_error_t(`OVL_FIRE_2STATE,"Test expression is not TRUE within specified maximum max_cks cycles from start event");
          end
        end
        if (action_on_new_start == `OVL_RESET_ON_NEW_START) begin : a_reset_on_new_start
          if (min_cks > 0) begin : a_assert_frame_reset_on_start_min_check
            A_ASSERT_FRAME_RESET_ON_START_MIN_CHECK_P:
            assert property (ASSERT_FRAME_RESET_ON_START_MIN_CHECK_P)
            else ovl_error_t(`OVL_FIRE_2STATE,"Test expression is TRUE before elapse of specified minimum min_cks cycles from start event");
          end
          if (max_cks > 0) begin : a_assert_frame_reset_on_start_max_check
            A_ASSERT_FRAME_RESET_ON_START_MAX_CHECK_P:
            assert property (ASSERT_FRAME_RESET_ON_START_MAX_CHECK_P)
            else ovl_error_t(`OVL_FIRE_2STATE,"Test expression is not TRUE within specified maximum max_cks cycles from start event");
          end
        end
        if (action_on_new_start == `OVL_ERROR_ON_NEW_START) begin : a_error_on_new_start
          A_ASSERT_FRAME_ERR_ON_START_P:
          assert property (ASSERT_FRAME_ERR_ON_START_P)
          else ovl_error_t(`OVL_FIRE_2STATE,"Illegal start event which has reoccured before completion of current window");
        end


`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
        A_ASSERT_FRAME_XZ_ON_START_P:
        assert property (ASSERT_FRAME_XZ_ON_START_P)
        else ovl_error_t(`OVL_FIRE_XCHECK,"start_event contains X or Z");

        if ( max_cks > 0 ) begin : a_assert_frame_xz_on_test_expr
          A_ASSERT_FRAME_XZ_ON_TEST_EXPR_P:
          assert property (ASSERT_FRAME_XZ_ON_TEST_EXPR_P)
          else ovl_error_t(`OVL_FIRE_XCHECK,"test_expr contains X or Z");

          if (action_on_new_start != `OVL_IGNORE_NEW_START ) begin : a_assert_frame_xz_on_new_start
            A_ASSERT_FRAME_XZ_ON_NEW_START_P:
            assert property (ASSERT_FRAME_XZ_ON_NEW_START_P)
            else ovl_error_t(`OVL_FIRE_XCHECK,"start_event contains X or Z");
          end
        end
        else if ( min_cks > 0 ) begin : a_assert_frame_min_xz_check
          A_ASSERT_FRAME_MIN_XZ_CHECK_P:
          assert property (ASSERT_FRAME_MIN_XZ_CHECK_P)
          else ovl_error_t(`OVL_FIRE_XCHECK,"test_expr contains X or Z");

          if (action_on_new_start != `OVL_IGNORE_NEW_START ) begin : a_assert_frame_xz_on_new_start
            A_ASSERT_FRAME_XZ_ON_NEW_START_P:
            assert property (ASSERT_FRAME_XZ_ON_NEW_START_P)
            else ovl_error_t(`OVL_FIRE_XCHECK,"start_event contains X or Z");
          end
        end
        else begin : a_assert_frame_xz_min0_max0 // ( (min_cks == 0) && (max_cks == 0) )
          A_ASSERT_FRAME_XZ_MIN0_MAX0_P:
          assert property (ASSERT_FRAME_XZ_MIN0_MAX0_P)
          else ovl_error_t(`OVL_FIRE_XCHECK,"test_expr contains X or Z");
        end
  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

      end
      `OVL_ASSUME_2STATE,
      `OVL_ASSUME: begin : ovl_assume
        if (min_cks == 0 && max_cks == 0) begin : m_assert_frame_min0_max0
          M_ASSERT_FRAME_MIN0_MAX0_P:
          assume property (ASSERT_FRAME_MIN0_MAX0_P);
        end
        if (action_on_new_start == `OVL_IGNORE_NEW_START ||
            action_on_new_start == `OVL_ERROR_ON_NEW_START) begin : m_ignore_or_error_on_new_start
          if (min_cks > 0) begin : m_assert_frame_min_check
            M_ASSERT_FRAME_MIN_CHECK_P:
            assume property (ASSERT_FRAME_MIN_CHECK_P);
          end
          if (max_cks > 0) begin : m_assert_frame_max_check
            M_ASSERT_FRAME_MAX_CHECK_P:
            assume property (ASSERT_FRAME_MAX_CHECK_P);
          end
        end
        if (action_on_new_start == `OVL_RESET_ON_NEW_START) begin : m_reset_on_new_start
          if (min_cks > 0) begin : m_assert_frame_reset_on_start_min_check
            M_ASSERT_FRAME_RESET_ON_START_MIN_CHECK_P:
            assume property (ASSERT_FRAME_RESET_ON_START_MIN_CHECK_P);
          end
          if (max_cks > 0) begin : m_assert_frame_reset_on_start_max_checK
            M_ASSERT_FRAME_RESET_ON_START_MAX_CHECK_P:
            assume property (ASSERT_FRAME_RESET_ON_START_MAX_CHECK_P);
          end
        end
        if (action_on_new_start == `OVL_ERROR_ON_NEW_START) begin : m_error_on_new_start
          M_ASSERT_FRAME_ERR_ON_START_P:
          assume property (ASSERT_FRAME_ERR_ON_START_P);
        end


`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
        M_ASSERT_FRAME_XZ_ON_START_P:
        assume property (ASSERT_FRAME_XZ_ON_START_P);

        if ( max_cks > 0 ) begin : m_assert_frame_xz_on_test_expr
          M_ASSERT_FRAME_XZ_ON_TEST_EXPR_P:
          assume property (ASSERT_FRAME_XZ_ON_TEST_EXPR_P);

          if (action_on_new_start != `OVL_IGNORE_NEW_START ) begin : m_assert_frame_xz_on_new_start_p
            M_ASSERT_FRAME_XZ_ON_NEW_START_P:
            assume property (ASSERT_FRAME_XZ_ON_NEW_START_P);
          end
        end
        else if ( min_cks > 0 ) begin : m_assert_frame_min_xz_check
          M_ASSERT_FRAME_MIN_XZ_CHECK_P:
          assume property (ASSERT_FRAME_MIN_XZ_CHECK_P);

          if (action_on_new_start != `OVL_IGNORE_NEW_START ) begin : m_assert_frame_xz_on_new_start
            M_ASSERT_FRAME_XZ_ON_NEW_START_P:
            assume property (ASSERT_FRAME_XZ_ON_NEW_START_P);
          end
        end
        else begin : m_assert_frame_xz_min0_max0 // ( (min_cks == 0) && (max_cks == 0) )
          M_ASSERT_FRAME_XZ_MIN0_MAX0_P:
          assume property (ASSERT_FRAME_XZ_MIN0_MAX0_P);
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

  generate

    if (coverage_level != `OVL_COVER_NONE) begin : ovl_cover
     if (OVL_COVER_BASIC_ON) begin : ovl_cover_basic

      cover_frame_start:
      cover property (@(posedge clk) (`OVL_RESET_SIGNAL != 1'b0 &&
                                      ($rose(start_event))))
                     ovl_cover_t("start_event covered");
     end
    end

  endgenerate

`endif // OVL_COVER_ON
