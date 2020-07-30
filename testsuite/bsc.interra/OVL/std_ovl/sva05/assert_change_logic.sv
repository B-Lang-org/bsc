// Accellera Standard V2.8.1 Open Verification Library (OVL).
// Accellera Copyright (c) 2005-2014. All rights reserved.

`ifdef OVL_SHARED_CODE

  reg window = 0;
  integer i = 0;

  always @ (posedge clk) begin
    if (`OVL_RESET_SIGNAL != 1'b0) begin
      if (!window && start_event == 1'b1) begin
        window <= 1'b1;
        i <= num_cks;
      end
      else if (window) begin
        if (i == 1 && (action_on_new_start != `OVL_RESET_ON_NEW_START || start_event != 1'b1))
          window <= 1'b0;

        if (action_on_new_start == `OVL_RESET_ON_NEW_START && start_event == 1'b1)
          i <= num_cks;
        else if (i != 1)
          i <= i - 1;
      end // if (window)
    end
    else begin
      window <= 1'b0;
      i <= 0;
    end
  end

`endif // OVL_SHARED_CODE

`ifdef OVL_ASSERT_ON

  property ASSERT_CHANGE_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  (start_event && !window) |-> (##[1:num_cks] !$stable(test_expr));
  endproperty

  property ASSERT_CHANGE_RESET_ON_START_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  (start_event) |=> (1'b1 [*0:num_cks-1] ##1
                     (!$stable(test_expr) || start_event));
  endproperty

  property ASSERT_CHANGE_ERR_ON_START_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  window |-> !start_event;
  endproperty


`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
  property ASSERT_CHANGE_XZ_ON_START_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  !(window) |-> (!($isunknown(start_event)));
  endproperty

  property ASSERT_CHANGE_XZ_ON_NEW_START_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  (window) |-> (!($isunknown(start_event)));
  endproperty

  property ASSERT_CHANGE_XZ_ON_TEST_EXPR_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  (window || start_event) |-> (!($isunknown(test_expr)));
  endproperty
  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

  generate

    case (property_type)
      `OVL_ASSERT_2STATE,
      `OVL_ASSERT: begin : ovl_assert
        if (action_on_new_start != `OVL_RESET_ON_NEW_START) begin : not_ovl_reset_on_new_start
          A_ASSERT_CHANGE_P:
          assert property (ASSERT_CHANGE_P)
          else ovl_error_t(`OVL_FIRE_2STATE,"Test expression did not change value within num_cks cycles after start event");
	end : not_ovl_reset_on_new_start
	if (action_on_new_start == `OVL_RESET_ON_NEW_START) begin : ovl_reset_on_new_start
          A_ASSERT_CHANGE_RESET_ON_START_P:
          assert property (ASSERT_CHANGE_RESET_ON_START_P)
          else ovl_error_t(`OVL_FIRE_2STATE,"Start event evaluated TRUE before test expression changed");
	end : ovl_reset_on_new_start
        if (action_on_new_start == `OVL_ERROR_ON_NEW_START) begin : ovl_error_on_new_start
          A_ASSERT_CHANGE_ERR_ON_START_P:
          assert property (ASSERT_CHANGE_ERR_ON_START_P)
          else ovl_error_t(`OVL_FIRE_2STATE,"Illegal re-occurance of start event");
	end : ovl_error_on_new_start

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
           A_ASSERT_CHANGE_XZ_ON_START_P:
           assert property (ASSERT_CHANGE_XZ_ON_START_P)
           else ovl_error_t(`OVL_FIRE_XCHECK,"start_event contains X or Z");
	  if (action_on_new_start != `OVL_IGNORE_NEW_START) begin : ovl_ignore_new_start
           A_ASSERT_CHANGE_XZ_ON_NEW_START_P:
           assert property (ASSERT_CHANGE_XZ_ON_NEW_START_P)
           else ovl_error_t(`OVL_FIRE_XCHECK,"start_event contains X or Z");
	  end : ovl_ignore_new_start
         A_ASSERT_CHANGE_XZ_ON_TEST_EXPR_P:
         assert property (ASSERT_CHANGE_XZ_ON_TEST_EXPR_P)
         else ovl_error_t(`OVL_FIRE_XCHECK,"test_expr contains X or Z");
  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

      end
      `OVL_ASSUME_2STATE,
      `OVL_ASSUME: begin : ovl_assume
        if (action_on_new_start != `OVL_RESET_ON_NEW_START)
          M_ASSERT_CHANGE_P:
          assume property (ASSERT_CHANGE_P);
        if (action_on_new_start == `OVL_RESET_ON_NEW_START)
          M_ASSERT_CHANGE_RESET_ON_START_P:
          assume property (ASSERT_CHANGE_RESET_ON_START_P);
        if (action_on_new_start == `OVL_ERROR_ON_NEW_START)
          M_ASSERT_CHANGE_ERR_ON_START_P:
          assume property (ASSERT_CHANGE_ERR_ON_START_P);


`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
           M_ASSERT_CHANGE_XZ_ON_START_P:
           assume property (ASSERT_CHANGE_XZ_ON_START_P);
         if (action_on_new_start != `OVL_IGNORE_NEW_START)
           M_ASSERT_CHANGE_XZ_ON_NEW_START_P:
           assume property (ASSERT_CHANGE_XZ_ON_NEW_START_P);
           M_ASSERT_CHANGE_XZ_ON_TEST_EXPR_P:
           assume property (ASSERT_CHANGE_XZ_ON_TEST_EXPR_P);
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

    cover_window_close:
    cover property (@(posedge clk) ( (`OVL_RESET_SIGNAL != 1'b0) &&
                   window && (i == 1 && (action_on_new_start != `OVL_RESET_ON_NEW_START || start_event != 1'b1))) )
                   ovl_cover_t("window_close covered");
  end //basic coverage

   if (OVL_COVER_CORNER_ON) begin : ovl_cover_corner

    if (action_on_new_start == `OVL_RESET_ON_NEW_START) begin : ovl_cover_window_resets
      cover_window_resets:
      cover property (@(posedge clk) ( (`OVL_RESET_SIGNAL != 1'b0) &&
                     start_event && window) )
                     ovl_cover_t("window_resets covered");
    end
   end //corner coverage

 end // OVL_COVER_NONE

endgenerate

`endif // OVL_COVER_ON
