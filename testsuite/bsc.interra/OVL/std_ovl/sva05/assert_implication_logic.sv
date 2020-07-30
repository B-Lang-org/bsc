// Accellera Standard V2.8.1 Open Verification Library (OVL).
// Accellera Copyright (c) 2005-2014. All rights reserved.




`ifdef OVL_ASSERT_ON

  property ASSERT_IMPLICATION_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  antecedent_expr |-> consequent_expr;
  endproperty


`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
  property ASSERT_IMPLICATION_XZ_ON_ANT_EXP_P;
  @ (posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  (!consequent_expr) |-> (!($isunknown(antecedent_expr)));
  endproperty

  property ASSERT_IMPLICATION_XZ_ON_CON_EXP_P;
  @ (posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  antecedent_expr |-> (!($isunknown(consequent_expr)));
  endproperty
  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

  generate

    case (property_type)
      `OVL_ASSERT_2STATE,
      `OVL_ASSERT: begin : ovl_assert
        A_ASSERT_IMPLICATION_P: assert property (ASSERT_IMPLICATION_P)
                                else ovl_error_t(`OVL_FIRE_2STATE,"Antecedent does not have consequent");

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
        A_ASSERT_IMPLICATION_XZ_ON_ANT_EXP_P:
        assert property (ASSERT_IMPLICATION_XZ_ON_ANT_EXP_P)
        else ovl_error_t(`OVL_FIRE_XCHECK,"antecedent_expr contains X or Z");

        A_ASSERT_IMPLICATION_XZ_ON_CON_EXP_P:
        assert property (ASSERT_IMPLICATION_XZ_ON_CON_EXP_P)
        else ovl_error_t(`OVL_FIRE_XCHECK,"consequent_expr contains X or Z");
  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

      end

      `OVL_ASSUME_2STATE,
      `OVL_ASSUME: begin : ovl_assume
        M_ASSERT_IMPLICATION_P: assume property (ASSERT_IMPLICATION_P);

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
        M_ASSERT_IMPLICATION_XZ_ON_ANT_EXP_P:
        assume property (ASSERT_IMPLICATION_XZ_ON_ANT_EXP_P);

        M_ASSERT_IMPLICATION_XZ_ON_CON_EXP_P:
        assume property (ASSERT_IMPLICATION_XZ_ON_CON_EXP_P);
  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

      end
      `OVL_IGNORE : begin : ovl_ignore
        // do nothing
      end

      default     : initial ovl_error_t(`OVL_FIRE_2STATE,"");
    endcase

  endgenerate

`endif // OVL_ASSERT_ON

`ifdef OVL_COVER_ON

  generate

    if (coverage_level != `OVL_COVER_NONE) begin : ovl_cover
     if (OVL_COVER_BASIC_ON) begin : ovl_cover_basic

      cover_antecedent:
      cover property (@(posedge clk) ( (`OVL_RESET_SIGNAL != 1'b0) &&
                     antecedent_expr) )
                     ovl_cover_t("antecedent covered");

     end
    end

  endgenerate

`endif // OVL_COVER_ON
