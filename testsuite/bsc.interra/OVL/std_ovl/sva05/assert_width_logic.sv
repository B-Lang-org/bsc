// Accellera Standard V2.8.1 Open Verification Library (OVL).
// Accellera Copyright (c) 2005-2014. All rights reserved.

`ifdef OVL_ASSERT_ON

  property ASSERT_WIDTH_MIN_CHECK_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  ##1 $rose(test_expr) |-> (test_expr[*min_cks]);
  endproperty

  property ASSERT_WIDTH_MAX_CHECK_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  ##1 $rose(test_expr) |-> (test_expr[*1:(max_cks > 0 ? max_cks : 2)]) ##1 (!test_expr);
  endproperty

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
  property ASSERT_WIDTH_XZ_ON_TEST_EXPR_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  (!($isunknown(test_expr)));
  endproperty
  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

  generate

    case (property_type)
      `OVL_ASSERT_2STATE,
      `OVL_ASSERT: begin : ovl_assert
        if (min_cks > 0) begin : a_assert_width_min_check
          A_ASSERT_WIDTH_MIN_CHECK_P: assert property (ASSERT_WIDTH_MIN_CHECK_P)
                                      else ovl_error_t(`OVL_FIRE_2STATE,"Test expression was held TRUE for less than specified minimum min_cks cycles");
        end
        if (max_cks > 0) begin : a_assert_width_max_check
          A_ASSERT_WIDTH_MAX_CHECK_P: assert property (ASSERT_WIDTH_MAX_CHECK_P)
                                      else ovl_error_t(`OVL_FIRE_2STATE,"Test expression was held TRUE for more than specified maximum max_cks cycles");
        end


`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
         A_ASSERT_WIDTH_XZ_ON_TEST_EXPR_P:
         assert property (ASSERT_WIDTH_XZ_ON_TEST_EXPR_P)
         else ovl_error_t(`OVL_FIRE_XCHECK,"test_expr contains X or Z");
  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

      end
      `OVL_ASSUME_2STATE,
      `OVL_ASSUME: begin : ovl_assume
        if (min_cks > 0) begin : m_assert_width_min_check
          M_ASSERT_WIDTH_MIN_CHECK_P: assume property (ASSERT_WIDTH_MIN_CHECK_P);
        end
        if (max_cks > 0) begin : m_assert_width_max_check
          M_ASSERT_WIDTH_MAX_CHECK_P: assume property (ASSERT_WIDTH_MAX_CHECK_P);
        end


`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
         M_ASSERT_WIDTH_XZ_ON_TEST_EXPR_P:
         assume property (ASSERT_WIDTH_XZ_ON_TEST_EXPR_P);
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

      cover_test_expr_asserts:
      cover property (@(posedge clk) ( (`OVL_RESET_SIGNAL != 1'b0) &&
                                       $rose(test_expr)
                                     )
                     )
                     ovl_cover_t("test_expr_asserts covered");
     end

     if (OVL_COVER_CORNER_ON) begin : ovl_cover_corner
      if (min_cks > 0) begin : ovl_cover_test_expr_asserted_for_min_cks

       cover_test_expr_asserted_for_min_cks:
       cover property (@(posedge clk) (`OVL_RESET_SIGNAL != 1'b0) throughout
                                      ($rose(test_expr)
                                      ##0
                                      (test_expr[*min_cks])
                                      ##1
                                      (!test_expr)
                                     )
                      )
                      ovl_cover_t("test_expr_asserted_for_min_cks covered");
      end

      if (max_cks > 0) begin : ovl_cover_test_expr_asserted_for_max_cks

       cover_test_expr_asserted_for_max_cks:
       cover property (@(posedge clk) (`OVL_RESET_SIGNAL != 1'b0) throughout
                                      ($rose(test_expr)
                                      ##0
                                      (test_expr[*max_cks])
                                      ##1
                                      (!test_expr)
                                     )
                      )
                      ovl_cover_t("test_expr_asserted_for_max_cks covered");
      end

     end //corner coverage
    end

endgenerate

`endif // OVL_COVER_ON

