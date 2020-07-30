// Accellera Standard V2.8.1 Open Verification Library (OVL).
// Accellera Copyright (c) 2005-2014. All rights reserved.



`ifdef OVL_ASSERT_ON

 wire xzcheck_enable;
 reg xzcheck_window = 0;

`ifdef OVL_XCHECK_OFF
  assign xzcheck_enable = 1'b0;
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    assign xzcheck_enable = 1'b0;
  `else
    assign xzcheck_enable = 1'b1;

    always @ (posedge clk)
      begin
        if (reset_n != 1'b0)
          begin
            if (!xzcheck_window && start_event == 1'b1)
              xzcheck_window <= 1'b1;
            else if (xzcheck_window && end_event == 1'b1)
              xzcheck_window <= 1'b0;
          end
        else
          begin
            xzcheck_window <= 1'b0;
          end
      end

  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

 generate
   case (property_type)
     `OVL_ASSERT_2STATE,
     `OVL_ASSERT: begin: assert_checks
                   assert_window_assert
                   assert_window_assert (
                       .clk(clk),
                       .reset_n(`OVL_RESET_SIGNAL),
                       .test_expr(test_expr),
                       .start_event(start_event),
                       .end_event(end_event),
                       .xzcheck_window(xzcheck_window),
                       .xzcheck_enable(xzcheck_enable));
                  end
     `OVL_ASSUME_2STATE,
     `OVL_ASSUME: begin: assume_checks
                   assert_window_assume
                   assert_window_assume (
                       .clk(clk),
                       .reset_n(`OVL_RESET_SIGNAL),
                       .test_expr(test_expr),
                       .start_event(start_event),
                       .end_event(end_event),
                       .xzcheck_window(xzcheck_window),
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
          assert_window_cover #(
                       .OVL_COVER_BASIC_ON(OVL_COVER_BASIC_ON))
          assert_window_cover (
                       .clk(clk),
                       .reset_n(`OVL_RESET_SIGNAL),
                       .test_expr(test_expr),
                       .start_event(start_event),
                       .end_event(end_event));
   end
 endgenerate
`endif

`endmodule //Required to pair up with already used "`module" in file assert_window.vlib

//Module to be replicated for assert checks
//This module is bound to a PSL vunits with assert checks
module assert_window_assert (clk, reset_n, test_expr, start_event, end_event, xzcheck_window, xzcheck_enable);
       input clk, reset_n, test_expr, start_event, end_event, xzcheck_window, xzcheck_enable;
endmodule

//Module to be replicated for assume checks
//This module is bound to a PSL vunits with assume checks
module assert_window_assume (clk, reset_n, test_expr, start_event, end_event, xzcheck_window, xzcheck_enable);
       input clk, reset_n, test_expr, start_event, end_event, xzcheck_window, xzcheck_enable;
endmodule

//Module to be replicated for cover properties
//This module is bound to a PSL vunit with cover properties
module assert_window_cover (clk, reset_n, test_expr, start_event, end_event);
       parameter OVL_COVER_BASIC_ON = 1;
       input clk, reset_n, test_expr, start_event, end_event;
endmodule
