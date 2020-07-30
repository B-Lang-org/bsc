// Accellera Standard V2.8.1 Open Verification Library (OVL).
// Accellera Copyright (c) 2005-2014. All rights reserved.



`ifdef OVL_ASSERT_ON

  property ASSERT_DELTA_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  (!$stable(test_expr) && $past(`OVL_RESET_SIGNAL)) |-> ((((({1'b0,$past(test_expr)} - {1'b0,test_expr}) & ({1'b0,{width{1'b1}}})) >= min) &&
                                                             ((({1'b0,$past(test_expr)} - {1'b0,test_expr}) & ({1'b0,{width{1'b1}}})) <= max)
                                                            ) ||
                                                            (((({1'b0,test_expr} - {1'b0,$past(test_expr)}) & ({1'b0,{width{1'b1}}})) >= min) &&
                                                             ((({1'b0,test_expr} - {1'b0,$past(test_expr)}) & ({1'b0,{width{1'b1}}})) <= max)
                                                            )
                                                           );
  endproperty


`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
  property ASSERT_DELTA_XZ_ON_TEST_EXPR_P;
  @ (posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  ((!($isunknown(test_expr))));
  endproperty
  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

  generate

    case (property_type)
      `OVL_ASSERT_2STATE,
      `OVL_ASSERT: begin : ovl_assert
        A_ASSERT_DELTA_P:
        assert property (ASSERT_DELTA_P) else ovl_error_t(`OVL_FIRE_2STATE,"Test expression changed by a delta value not in the range specified by min and max");


`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
        A_ASSERT_DELTA_XZ_ON_TEST_EXPR_P:
        assert property (ASSERT_DELTA_XZ_ON_TEST_EXPR_P)
        else ovl_error_t(`OVL_FIRE_XCHECK,"test_expr contains X or Z");
  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

      end

      `OVL_ASSUME_2STATE,
      `OVL_ASSUME: begin : ovl_assume
        M_ASSERT_DELTA_P: assume property (ASSERT_DELTA_P);

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
        M_ASSERT_DELTA_XZ_ON_TEST_EXPR_P:
        assume property (ASSERT_DELTA_XZ_ON_TEST_EXPR_P);
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

      cover_test_expr_change:
      cover property (@(posedge clk) ( (`OVL_RESET_SIGNAL != 1'b0) &&
                     ($past(`OVL_RESET_SIGNAL) != 1'b0) &&
                     !$stable(test_expr) ) )
                     ovl_cover_t("test_expr_change covered");
     end

     if (OVL_COVER_CORNER_ON) begin : ovl_cover_corner

      cover_test_expr_delta_at_min:
      cover property (@(posedge clk) ( (`OVL_RESET_SIGNAL != 1'b0) &&
                     ($past(`OVL_RESET_SIGNAL) != 1'b0) &&
                     !$stable(test_expr) &&
                     (((({1'b0,$past(test_expr)} - {1'b0,test_expr}) & ({1'b0,{width{1'b1}}})) == min) ||
                     ((({1'b0,test_expr} - {1'b0,$past(test_expr)}) & ({1'b0,{width{1'b1}}})) == min) ) ) )
                     ovl_cover_t("test_expr_delta_at_min covered");

      cover_test_expr_delta_at_max:
      cover property (@(posedge clk) ( (`OVL_RESET_SIGNAL != 1'b0) &&
                     ($past(`OVL_RESET_SIGNAL) != 1'b0) && 
                     !$stable(test_expr) &&
                     (((({1'b0,$past(test_expr)} - {1'b0,test_expr}) & ({1'b0,{width{1'b1}}})) == max) ||
                     ((({1'b0,test_expr} - {1'b0,$past(test_expr)}) & ({1'b0,{width{1'b1}}})) == max) ) ) )
                     ovl_cover_t("test_expr_delta_at_max covered");
     end
    end

  endgenerate

`endif // OVL_COVER_ON
