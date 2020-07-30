// Accellera Standard V2.8.1 Open Verification Library (OVL).
// Accellera Copyright (c) 2005-2014. All rights reserved.

  bit fire_2state, fire_xcheck, fire_cover;

`ifdef OVL_ASSERT_ON

  always @(posedge clk)
    fire_2state = 0;

  property ASSERT_RANGE_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  (((test_expr >= min) && (test_expr <= max)) != 1'b0);
  endproperty


`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else

    always @(posedge clk)
      fire_xcheck = 0;

    property ASSERT_RANGE_XZ_ON_TEST_EXPR_P;
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
        A_ASSERT_RANGE_P:
        assert property (ASSERT_RANGE_P)
        else begin
          ovl_error_t(`OVL_FIRE_2STATE,"Test expression evaluates to a value outside the range specified by parameters min and max");
          fire_2state = ovl_fire_2state_f(property_type);
        end

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
       A_ASSERT_RANGE_XZ_ON_TEST_EXPR_P:
       assert property (ASSERT_RANGE_XZ_ON_TEST_EXPR_P)
       else begin
         ovl_error_t(`OVL_FIRE_XCHECK,"test_expr contains X or Z");
         fire_xcheck = ovl_fire_xcheck_f(property_type);
       end
  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

      end
      `OVL_ASSUME_2STATE,
      `OVL_ASSUME: begin : ovl_assume
        M_ASSERT_RANGE_P: assume property (ASSERT_RANGE_P);

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
         M_ASSERT_RANGE_XZ_ON_TEST_EXPR_P:
         assume property (ASSERT_RANGE_XZ_ON_TEST_EXPR_P);
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
     if (OVL_COVER_SANITY_ON) begin : ovl_cover_sanity

      cover_test_expr_change:
      cover property (@(posedge clk) ( (`OVL_RESET_SIGNAL != 1'b0) &&
                     ($past(`OVL_RESET_SIGNAL) != 1'b0) && 
                     !$stable(test_expr) ) ) begin
                       ovl_cover_t("test_expr_change covered");
                       fire_cover = ovl_fire_cover_f(coverage_level);
                     end
     end //sanity coverage

     if (OVL_COVER_CORNER_ON) begin : ovl_cover_corner

      cover_test_expr_at_min:
      cover property (@(posedge clk) ( (`OVL_RESET_SIGNAL != 1'b0) &&
                     ($past(`OVL_RESET_SIGNAL) != 1'b0) &&
                     $rose(test_expr == min) ) ) begin
                       ovl_cover_t("test_expr_at_min covered");
                       fire_cover = ovl_fire_cover_f(coverage_level);
                     end
      cover_test_expr_at_max:
      cover property (@(posedge clk) ( (`OVL_RESET_SIGNAL != 1'b0) &&
                     ($past(`OVL_RESET_SIGNAL) != 1'b0) &&
                     $rose(test_expr == max) ) ) begin
                       ovl_cover_t("test_expr_at_max covered");
                       fire_cover = ovl_fire_cover_f(coverage_level);
                     end
     end
    end

endgenerate

`endif // OVL_COVER_ON

