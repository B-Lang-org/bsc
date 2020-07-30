// Accellera Standard V2.8.1 Open Verification Library (OVL).
// Accellera Copyright (c) 2005-2014. All rights reserved.



`ifdef OVL_SHARED_CODE

  reg window = 0;

  always @ (posedge clk) begin
    if (`OVL_RESET_SIGNAL != 1'b0) begin
      if (!window && start_event == 1'b1)
        window <= 1'b1;
      else if (window && end_event == 1'b1)
        window <= 1'b0;
    end
    else begin
      window <= 1'b0;
    end
  end

`endif // OVL_SHARED_CODE

`ifdef OVL_ASSERT_ON

  property ASSERT_WIN_UNCHANGE_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  (start_event && !window) ##1 (!(end_event && $stable(test_expr)))[*1:$] |-> $stable(test_expr);
  endproperty

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
  property ASSERT_WIN_UNCHANGE_XZ_ON_START_EVENT_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  !(window) |-> (!($isunknown(start_event)));
  endproperty

  property ASSERT_WIN_UNCHANGE_XZ_ON_TEST_EXPR_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  (window || start_event) |-> (!($isunknown(test_expr)));
  endproperty

  property ASSERT_WIN_UNCHANGE_XZ_ON_END_EVENT_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  (window) |-> (!($isunknown(end_event)));
  endproperty
  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

  generate

    case (property_type)
      `OVL_ASSERT_2STATE,
      `OVL_ASSERT: begin : ovl_assert
        A_ASSERT_WIN_UNCHANGE_P: assert property (ASSERT_WIN_UNCHANGE_P)
                                 else ovl_error_t(`OVL_FIRE_2STATE,"Test expression has changed value before the event window closes");

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
        A_ASSERT_WIN_UNCHANGE_XZ_ON_START_EVENT_P:
          assert property (ASSERT_WIN_UNCHANGE_XZ_ON_START_EVENT_P)
          else ovl_error_t(`OVL_FIRE_XCHECK,"start_event contains X or Z");
        A_ASSERT_WIN_UNCHANGE_XZ_ON_TEST_EXPR_P:
          assert property (ASSERT_WIN_UNCHANGE_XZ_ON_TEST_EXPR_P)
          else ovl_error_t(`OVL_FIRE_XCHECK,"test_expr contains X or Z");
        A_ASSERT_WIN_UNCHANGE_XZ_ON_END_EVENT_P:
          assert property (ASSERT_WIN_UNCHANGE_XZ_ON_END_EVENT_P)
          else ovl_error_t(`OVL_FIRE_XCHECK,"end_event contains X or Z");
  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

      end
      `OVL_ASSUME_2STATE,
      `OVL_ASSUME: begin : ovl_assume
        M_ASSERT_WIN_UNCHANGE_P: assume property (ASSERT_WIN_UNCHANGE_P);

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
        M_ASSERT_WIN_UNCHANGE_XZ_ON_START_EVENT_P:
          assume property (ASSERT_WIN_UNCHANGE_XZ_ON_START_EVENT_P);
        M_ASSERT_WIN_UNCHANGE_XZ_ON_TEST_EXPR_P:
          assume property (ASSERT_WIN_UNCHANGE_XZ_ON_TEST_EXPR_P);
        M_ASSERT_WIN_UNCHANGE_XZ_ON_END_EVENT_P:
          assume property (ASSERT_WIN_UNCHANGE_XZ_ON_END_EVENT_P);
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

      cover_window_open:
      cover property (@(posedge clk) ( (`OVL_RESET_SIGNAL != 1'b0) &&
                     start_event && !window) )
                     ovl_cover_t("window_open covered");

      cover_window:
      cover property (@(posedge clk) (`OVL_RESET_SIGNAL != 1'b0) throughout
                     ((start_event && !window) ##1
                     (!end_event && window) [*0:$] ##1
                     (end_event && window)) )
                     ovl_cover_t("window covered");
     end //basic coverage
    end

endgenerate

`endif // OVL_COVER_ON

