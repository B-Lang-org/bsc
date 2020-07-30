// Accellera Standard V2.8.1 Open Verification Library (OVL).
// Accellera Copyright (c) 2005-2014. All rights reserved.




`ifdef OVL_ASSERT_ON

  property ASSERT_NO_TRANSITION_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  (test_expr == start_state) |=> (test_expr != $past(next_state));
  endproperty


`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
  property ASSERT_NO_TRANSITION_XZ_ON_TEST_EXPR_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
    (!($isunknown(test_expr)));
  endproperty

  property ASSERT_NO_TRANSITION_XZ_ON_START_STATE_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
    (!($isunknown(start_state)));
  endproperty

  property ASSERT_NO_TRANSITION_XZ_ON_NEXT_STATE_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
    (test_expr == start_state) |-> (!($isunknown(next_state)));
  endproperty
  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

  generate

    case (property_type)
      `OVL_ASSERT_2STATE,
      `OVL_ASSERT: begin : ovl_assert
        A_ASSERT_NO_TRANSITION_P: assert property (ASSERT_NO_TRANSITION_P)
                                  else ovl_error_t(`OVL_FIRE_2STATE,"Test expression transitioned from value equal to start_state to a value equal to next_state");


`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
        A_ASSERT_NO_TRANSITION_XZ_ON_TEST_EXPR_P:
          assert property (ASSERT_NO_TRANSITION_XZ_ON_TEST_EXPR_P)
          else ovl_error_t(`OVL_FIRE_XCHECK,"test_expr contains X or Z");

        A_ASSERT_NO_TRANSITION_XZ_ON_START_STATE_P:
          assert property (ASSERT_NO_TRANSITION_XZ_ON_START_STATE_P)
          else ovl_error_t(`OVL_FIRE_XCHECK,"start_state contains X or Z");

        A_ASSERT_NO_TRANSITION_XZ_ON_NEXT_STATE_P:
          assert property (ASSERT_NO_TRANSITION_XZ_ON_NEXT_STATE_P)
          else ovl_error_t(`OVL_FIRE_XCHECK,"next_state contains X or Z");
  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF



      end
      `OVL_ASSUME_2STATE,
      `OVL_ASSUME: begin : ovl_assume
        M_ASSERT_NO_TRANSITION_P: assume property (ASSERT_NO_TRANSITION_P);


`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
        M_ASSERT_NO_TRANSITION_XZ_ON_TEST_EXPR_P:
          assume property (ASSERT_NO_TRANSITION_XZ_ON_TEST_EXPR_P);

        M_ASSERT_NO_TRANSITION_XZ_ON_START_STATE_P:
          assume property (ASSERT_NO_TRANSITION_XZ_ON_START_STATE_P);

        M_ASSERT_NO_TRANSITION_XZ_ON_NEXT_STATE_P:
          assume property (ASSERT_NO_TRANSITION_XZ_ON_NEXT_STATE_P);
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

      cover_start_state:
      cover property (@(posedge clk) ( (`OVL_RESET_SIGNAL != 1'b0) &&
                     (test_expr == start_state)) )
                     ovl_cover_t("start_state covered");
     end
    end

endgenerate

`endif // OVL_COVER_ON
