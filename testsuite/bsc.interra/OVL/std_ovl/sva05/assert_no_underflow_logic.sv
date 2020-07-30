// Accellera Standard V2.8.1 Open Verification Library (OVL).
// Accellera Copyright (c) 2005-2014. All rights reserved.




`ifdef OVL_ASSERT_ON

  property ASSERT_NO_UNDERFLOW_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  (test_expr == min) |=> ((test_expr < max) && (test_expr >= min));
  endproperty


`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
  property ASSERT_NO_UNDERFLOW_XZ_ON_TEST_EXPR_P;
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
        A_ASSERT_NO_UNDERFLOW_P: assert property (ASSERT_NO_UNDERFLOW_P)
                                 else ovl_error_t(`OVL_FIRE_2STATE,"Test expression changed value from allowed minimum value min to a value in the range min-1 to max");

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
        A_ASSERT_NO_UNDERFLOW_XZ_ON_TEST_EXPR_P:
        assert property (ASSERT_NO_UNDERFLOW_XZ_ON_TEST_EXPR_P)
        else ovl_error_t(`OVL_FIRE_XCHECK,"test_expr contains X or Z");
  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF


      end
      `OVL_ASSUME_2STATE,
      `OVL_ASSUME: begin : ovl_assume
        M_ASSERT_NO_UNDERFLOW_P: assume property (ASSERT_NO_UNDERFLOW_P);

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
        M_ASSERT_NO_UNDERFLOW_XZ_ON_TEST_EXPR_P:
        assume property (ASSERT_NO_UNDERFLOW_XZ_ON_TEST_EXPR_P);

  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF


      end
      `OVL_IGNORE : begin : ovl_ignore
        // Do nothing;
      end
      default     : initial ovl_error_t(`OVL_FIRE_2STATE,"");
    endcase

  endgenerate

`endif // OVL_ASSERT_ON

`ifdef OVL_COVER_ON

generate

    if (coverage_level != `OVL_COVER_NONE) begin : ovl_cover
     if (OVL_COVER_BASIC_ON) begin : ovl_cover_basic

      cover_test_expr_at_min:
      cover property (@(posedge clk) ( (`OVL_RESET_SIGNAL != 1'b0) &&
                     $rose(test_expr == min) ))
                     ovl_cover_t("test_expr_at_min covered");
     end //basic coverege

     if (OVL_COVER_CORNER_ON) begin : ovl_cover_corner

      cover_test_expr_at_max:
      cover property (@(posedge clk) ( (`OVL_RESET_SIGNAL != 1'b0) &&
                     $rose(test_expr == max) ))
                     ovl_cover_t("test_expr_at_max covered");
     end //corner coverage
    end

endgenerate

`endif // OVL_COVER_ON
