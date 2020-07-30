// Accellera Standard V2.8.1 Open Verification Library (OVL).
// Accellera Copyright (c) 2005-2014. All rights reserved.


`ifdef OVL_ASSERT_ON

 wire xzcheck_enable;

`ifdef OVL_XCHECK_OFF
  assign xzcheck_enable = 1'b0;
`else
  assign xzcheck_enable = 1'b1;
`endif // OVL_XCHECK_OFF

 generate
   case (property_type)
     `OVL_ASSERT_2STATE,
     `OVL_ASSERT: begin: assert_checks
                    assert_never_unknown_async_assert #(
                       .width(width))
                    assert_never_unknown_async_assert (
                       .reset_n(`OVL_RESET_SIGNAL),
                       .test_expr(test_expr),
                       .xzcheck_enable(xzcheck_enable));
                  end

//Note: This is an unclocked/immediate assertion based checker
//      Immediate assertions may not assumptions.
//      Assume is only available in a concurrent (clocked) form of an 
//      assertion statement. Hence, this checker does not implement
//      assumption of the property.

     `OVL_IGNORE: begin: ovl_ignore
                    //do nothing
                  end
     default: initial ovl_error_t(`OVL_FIRE_2STATE,"");
   endcase
 endgenerate
`endif

`endmodule //Required to pair up with already used "`module" in file assert_never_unknown_async.vlib

//Module to be replicated for assert checks
//This module is bound to the PSL vunits with assert checks
module assert_never_unknown_async_assert (reset_n, test_expr, xzcheck_enable);
       parameter width = 8;
       input reset_n, xzcheck_enable;
       input [width-1:0] test_expr;
endmodule

