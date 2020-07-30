// Accellera Standard V2.8.1 Open Verification Library (OVL).
// Accellera Copyright (c) 2005-2014. All rights reserved.

  bit fire_2state, fire_xcheck, fire_cover;

`ifdef OVL_ASSERT_ON

  always @(posedge clk)
    fire_2state = 0;

  property ASSERT_ALWAYS_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)

`ifdef OVL_XCHECK_OFF
    !($isunknown(test_expr)) |->
`else
    //Do not check for unknown by default to improve performance
`endif
    test_expr;
  endproperty

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else

  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else

    always @(posedge clk)
      fire_xcheck = 0;

    property ASSERT_ALWAYS_XZ_ON_TEST_EXPR_P;
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
        A_ASSERT_ALWAYS_P:
        assert property (ASSERT_ALWAYS_P)
        else begin
          ovl_error_t(`OVL_FIRE_2STATE,"Test expression is FALSE");
          fire_2state = ovl_fire_2state_f(property_type);
        end

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
        A_ASSERT_ALWAYS_XZ_ON_TEST_EXPR_P:
        assert property (ASSERT_ALWAYS_XZ_ON_TEST_EXPR_P)
        else begin
          ovl_error_t(`OVL_FIRE_XCHECK,"test_expr contains X or Z");
          fire_xcheck = ovl_fire_xcheck_f(property_type);
        end
  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

      end

      `OVL_ASSUME_2STATE,
      `OVL_ASSUME: begin : ovl_assume
        M_ASSERT_ALWAYS_P: assume property (ASSERT_ALWAYS_P);

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
        M_ASSERT_ALWAYS_XZ_ON_TEST_EXPR_P:
        assume property (ASSERT_ALWAYS_XZ_ON_TEST_EXPR_P);
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

   // No coverpoint is specified for this component

`endif // OVL_COVER_ON

