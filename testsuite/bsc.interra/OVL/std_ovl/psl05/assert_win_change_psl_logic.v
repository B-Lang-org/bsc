// Accellera Standard V2.8.1 Open Verification Library (OVL).
// Accellera Copyright (c) 2005-2014. All rights reserved.



`ifdef OVL_SHARED_CODE

  reg window = 0;

  always @ (posedge clk) begin
    if (`OVL_RESET_SIGNAL != 1'b0) begin
      if (!window && start_event == 1'b1)
        window <= 1'b1;
      else if (window && end_event == 1'b1)
        window <= 1'b0;
    end
    else begin
      window <= 1'b0;
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

    wire xzdetect_test_expr;
    assign xzdetect_test_expr = ((^test_expr) ^ (^test_expr) == 1'b0);

  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

 generate
   case (property_type)
     `OVL_ASSERT_2STATE,
     `OVL_ASSERT: begin: assert_checks
         assert_win_change_assert #(
                       .width(width))
                assert_win_change_assert (
                       .clk(clk),
                       .reset_n(`OVL_RESET_SIGNAL),
                       .start_event(start_event),
                       .end_event(end_event),
                       .test_expr(test_expr),
                       .window(window),
                       .xzdetect_test_expr(xzdetect_test_expr),
                       .xzcheck_enable(xzcheck_enable));
                  end
     `OVL_ASSUME_2STATE,
     `OVL_ASSUME: begin: assume_checks
         assert_win_change_assume #(
                       .width(width))
                assert_win_change_assume (
                       .clk(clk),
                       .reset_n(`OVL_RESET_SIGNAL),
                       .start_event(start_event),
                       .end_event(end_event),
                       .test_expr(test_expr),
                       .window(window),
                       .xzdetect_test_expr(xzdetect_test_expr),
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
              assert_win_change_cover #(
                       .OVL_COVER_BASIC_ON(OVL_COVER_BASIC_ON))
                assert_win_change_cover (
                       .clk(clk),
                       .reset_n(`OVL_RESET_SIGNAL),
                       .start_event(start_event),
                       .end_event(end_event),
                       .window(window));
   end
 endgenerate
`endif

`endmodule //Required to pair up with already used "`module" in file assert_win_change.vlib

//Module to be replicated for assert checks
//This module is bound to a PSL vunits with assert checks
module assert_win_change_assert (clk, reset_n, start_event, end_event, test_expr, window,
                                 xzdetect_test_expr, xzcheck_enable);
       parameter width = 8;
       input clk, reset_n, start_event, end_event, window;
       input [width-1:0] test_expr;
       input xzdetect_test_expr, xzcheck_enable;
endmodule

//Module to be replicated for assume checks
//This module is bound to a PSL vunits with assume checks
module assert_win_change_assume (clk, reset_n, start_event, end_event, test_expr, window,
                                 xzdetect_test_expr, xzcheck_enable);
       parameter width = 8;
       input clk, reset_n, start_event, end_event, window;
       input [width-1:0] test_expr;
       input xzdetect_test_expr, xzcheck_enable;
endmodule


//Module to be replicated for cover properties
//This module is bound to a PSL vunit with cover properties
module assert_win_change_cover (clk, reset_n, start_event, end_event, window);
       parameter OVL_COVER_BASIC_ON = 1;
       input clk, reset_n, start_event, end_event, window;
endmodule
