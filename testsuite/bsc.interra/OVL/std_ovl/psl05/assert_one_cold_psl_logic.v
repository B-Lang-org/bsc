// Accellera Standard V2.8.1 Open Verification Library (OVL).
// Accellera Copyright (c) 2005-2014. All rights reserved.


`ifdef OVL_SHARED_CODE

 wire inactive_val = (inactive==`OVL_ALL_ONES) ? 1'b1 : 1'b0;

`endif

`ifdef OVL_ASSERT_ON

 wire xzcheck_enable;

`ifdef OVL_XCHECK_OFF
  assign xzcheck_enable = 1'b0;
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    assign xzcheck_enable = 1'b0;
  `else
    assign xzcheck_enable = 1'b1;
  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF


 generate
   case (property_type)
     `OVL_ASSERT_2STATE,
     `OVL_ASSERT: begin: assert_checks
                    assert_one_cold_assert #(
                       .width(width),
                       .inactive(inactive))
                    assert_one_cold_assert (
                       .clk(clk),
                       .reset_n(`OVL_RESET_SIGNAL),
                       .test_expr(test_expr),
                       .inactive_val(inactive_val),
                       .xzcheck_enable(xzcheck_enable));
                  end
     `OVL_ASSUME_2STATE,
     `OVL_ASSUME: begin: assume_checks
                    assert_one_cold_assume #(
                       .width(width),
                       .inactive(inactive))
                    assert_one_cold_assume (
                       .clk(clk),
                       .reset_n(`OVL_RESET_SIGNAL),
                       .test_expr(test_expr),
                       .inactive_val(inactive_val),
                       .xzcheck_enable(xzcheck_enable));
                  end
     `OVL_IGNORE: begin: ovl_ignore
                    //do nothing
                  end
     default: initial ovl_error_t(`OVL_FIRE_2STATE,"");
   endcase
 endgenerate
`endif

`ifdef OVL_COVER_ON

 reg [width-1:0] one_colds_checked;
 wire [width-1:0] test_expr_i = ~test_expr;
 wire [width-1:0] test_expr_i_1 = test_expr_i > 0 ? test_expr_i - {{width-1{1'b0}},1'b1} : 0;


 always @(posedge clk)
  if (`OVL_RESET_SIGNAL != 1'b1)
    one_colds_checked <= {width{1'b1}};
  else //check for known driven and zero one cold test_expr and update one_colds_checked
    one_colds_checked <= ((test_expr ^ test_expr)=={width{1'b0}}) &&
                         (((inactive > `OVL_ALL_ONES) || (test_expr!={width{inactive_val}})) &&
                          (!((test_expr_i == {width{1'b0}}) || (test_expr_i & test_expr_i_1) != {width{1'b0}}))) ?
                         one_colds_checked & test_expr : one_colds_checked;

 generate
  if (coverage_level != `OVL_COVER_NONE)
                  begin: cover_checks
                    assert_one_cold_cover #(
                       .width(width),
                       .inactive(inactive),
                       .OVL_COVER_SANITY_ON(OVL_COVER_SANITY_ON),
                       .OVL_COVER_CORNER_ON(OVL_COVER_CORNER_ON))
                    assert_one_cold_cover (
                       .clk(clk),
                       .reset_n(`OVL_RESET_SIGNAL),
                       .test_expr(test_expr),
                       .one_colds_checked(one_colds_checked),
                       .inactive_val(inactive_val));
                  end
 endgenerate

`endif

`endmodule //Required to pair up with already used "`module" in file assert_one_cold.vlib

//Module to be replicated for assert checks
//This module is bound to the PSL vunits with assert checks
module assert_one_cold_assert (clk, reset_n, test_expr, xzcheck_enable, inactive_val);
       parameter width = 8;
       parameter inactive = `OVL_ONE_COLD;
       input clk, reset_n, xzcheck_enable, inactive_val;
       input [width-1:0] test_expr;
endmodule

//Module to be replicated for assume checks
//This module is bound to a PSL vunits with assume checks
module assert_one_cold_assume (clk, reset_n, test_expr, xzcheck_enable, inactive_val);
       parameter width = 8;
       parameter inactive = `OVL_ONE_COLD;
       input clk, reset_n, xzcheck_enable, inactive_val;
       input [width-1:0] test_expr;
endmodule

//Module to be replicated for cover properties
//This module is bound to a PSL vunit with cover properties
module assert_one_cold_cover (clk, reset_n, test_expr, one_colds_checked, inactive_val);
       parameter width = 8;
       parameter inactive = `OVL_ONE_COLD;
       parameter OVL_COVER_SANITY_ON = 1;
       parameter OVL_COVER_CORNER_ON = 1;
       input clk, reset_n, inactive_val;
       input [width-1:0] test_expr, one_colds_checked;
endmodule
