// Accellera Standard V2.8.1 Open Verification Library (OVL).
// Accellera Copyright (c) 2005-2014. All rights reserved.

`ifdef OVL_SHARED_CODE

  integer i = 0;

  always @ (posedge clk) begin
    if (`OVL_RESET_SIGNAL != 1'b0) begin
      if (start_event == 1'b1) begin
        i <= num_cks;
      end
      else if (i > 1) begin
        i <= i - 1;
      end
    end
    else begin
      i <= 0;
    end
  end

`endif // OVL_SHARED_CODE

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
                   assert_next_assert #(
                       .num_cks(num_cks),
                       .check_overlapping(check_overlapping),
                       .check_missing_start(check_missing_start))
                   assert_next_assert (
                       .clk(clk),
                       .reset_n(`OVL_RESET_SIGNAL),
                       .test_expr(test_expr),
                       .start_event(start_event),
                       .no_overlapping(i <= 0),
                       .xzcheck_enable(xzcheck_enable));
                  end
     `OVL_ASSUME_2STATE,
     `OVL_ASSUME: begin: assume_checks
                   assert_next_assume #(
                       .num_cks(num_cks),
                       .check_overlapping(check_overlapping),
                       .check_missing_start(check_missing_start))
                   assert_next_assume (
                       .clk(clk),
                       .reset_n(`OVL_RESET_SIGNAL),
                       .test_expr(test_expr),
                       .start_event(start_event),
                       .no_overlapping(i <= 0),
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
 generate
  if (coverage_level != `OVL_COVER_NONE)
   begin: cover_checks
          assert_next_cover #(
                       .OVL_COVER_BASIC_ON(OVL_COVER_BASIC_ON),
                       .OVL_COVER_CORNER_ON(OVL_COVER_CORNER_ON))
          assert_next_cover (
                       .clk(clk),
                       .reset_n(`OVL_RESET_SIGNAL),
                       .test_expr(test_expr),
                       .start_event(start_event),
                       .no_overlapping(i <= 0));
   end
 endgenerate
`endif

`endmodule //Required to pair up with already used "`module" in file assert_next.vlib

//Module to be replicated for assert checks
//This module is bound to a PSL vunits with assert checks
module assert_next_assert (clk, reset_n, test_expr, start_event, no_overlapping, xzcheck_enable);
       parameter num_cks = 1;
       parameter check_overlapping = 1;
       parameter check_missing_start = 1;
       input clk, reset_n, test_expr, start_event, no_overlapping, xzcheck_enable;
endmodule

//Module to be replicated for assume checks
//This module is bound to a PSL vunits with assume checks
module assert_next_assume (clk, reset_n, test_expr, start_event, no_overlapping, xzcheck_enable);
       parameter num_cks = 1;
       parameter check_overlapping = 1;
       parameter check_missing_start = 1;
       input clk, reset_n, test_expr, start_event, no_overlapping, xzcheck_enable;
endmodule

//Module to be replicated for cover properties
//This module is bound to a PSL vunit with cover properties
module assert_next_cover (clk, reset_n, test_expr, start_event, no_overlapping);
       parameter OVL_COVER_BASIC_ON = 1;
       parameter OVL_COVER_CORNER_ON = 1;
       input clk, reset_n, test_expr, start_event, no_overlapping;
endmodule
