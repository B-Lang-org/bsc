// Accellera Standard V2.8.1 Open Verification Library (OVL).
// Accellera Copyright (c) 2005-2014. All rights reserved.



`ifdef OVL_ASSERT_ON

  generate

     case (property_type)

      `OVL_ASSERT_2STATE,
      `OVL_ASSERT: begin : ovl_assert

         always @(`OVL_RESET_SIGNAL or test_expr) begin
           if (`OVL_RESET_SIGNAL != 1'b0) begin
               A_ASSERT_PROPOSITION_P:
                 assert #0 (test_expr != 1'b0)
                 else ovl_error_t(`OVL_FIRE_2STATE,"Test expression is FALSE");
           end
         end // always

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else

         always @(`OVL_RESET_SIGNAL or test_expr) begin
           if (`OVL_RESET_SIGNAL != 1'b0) begin
             A_ASSERT_PROPOSITION_XZ_ON_TEST_P:
               assert #0 (!($isunknown(test_expr)))
               else ovl_error_t(`OVL_FIRE_XCHECK,"test_expr contains X or Z");
           end
         end

  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF
  
      end

//Note: This is an unclocked/immediate assertion based checker
//      As per IEEE 1800-2005 SV, immediate assertions can't be assumptions.
//      Assume is only available in a concurrent (clocked) form of an
//      assertion statement. Hence, this checker does not implement
//      assumption of the properties.

      `OVL_IGNORE : begin : ovl_ignore
        // do nothing;
      end

      default     : initial ovl_error_t(`OVL_FIRE_2STATE,"");

     endcase

  endgenerate

`endif // OVL_ASSERT_ON

