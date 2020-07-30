// Accellera Standard V2.8.1 Open Verification Library (OVL).
// Accellera Copyright (c) 2005-2014. All rights reserved.


  wire ignore_new_start   = (action_on_new_start == `OVL_IGNORE_NEW_START);
  wire reset_on_new_start = (action_on_new_start == `OVL_RESET_ON_NEW_START);
  wire error_on_new_start = (action_on_new_start == `OVL_ERROR_ON_NEW_START);


`ifdef OVL_SHARED_CODE

  reg window = 0;
  integer i = 0;

  always @ (posedge clk) begin
    if (`OVL_RESET_SIGNAL != 1'b0) begin
      if (!window && start_event == 1'b1) begin
        window <= 1'b1;
        i <= num_cks;
      end
      else if (window) begin
        if (i == 1 && (!reset_on_new_start || !start_event))
          window <= 1'b0;

        if (reset_on_new_start && start_event)
          i <= num_cks;
        else if (i != 1)
          i <= i - 1;
      end // if (window)
    end
    else begin
      window <= 1'b0;
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
         assert_change_assert #(
                       .width(width),
                       .num_cks(num_cks))
                assert_change_assert (
                       .clk(clk),
                       .reset_n(`OVL_RESET_SIGNAL),
                       .start_event(start_event),
                       .test_expr(test_expr),
                       .window(window),
                       .ignore_new_start(ignore_new_start),
                       .reset_on_new_start(reset_on_new_start),
                       .error_on_new_start(error_on_new_start),
                       .xzcheck_enable(xzcheck_enable));
                  end
     `OVL_ASSUME_2STATE,
     `OVL_ASSUME: begin: assume_checks
         assert_change_assume #(
                       .width(width),
                       .num_cks(num_cks))
                assert_change_assume (
                       .clk(clk),
                       .reset_n(`OVL_RESET_SIGNAL),
                       .start_event(start_event),
                       .test_expr(test_expr),
                       .window(window),
                       .ignore_new_start(ignore_new_start),
                       .reset_on_new_start(reset_on_new_start),
                       .error_on_new_start(error_on_new_start),
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
              assert_change_cover #(
                       .OVL_COVER_BASIC_ON(OVL_COVER_BASIC_ON),
                       .OVL_COVER_CORNER_ON(OVL_COVER_CORNER_ON))
                assert_change_cover (
                       .clk(clk),
                       .reset_n(`OVL_RESET_SIGNAL),
                       .start_event(start_event),
                       .window(window),
                       .reset_on_new_start(reset_on_new_start),
                       .window_close(i == 1)); // i == 1 means window is closing
   end
 endgenerate
`endif

`endmodule //Required to pair up with already used "`module" in file assert_change.vlib

//Module to be replicated for assert checks
//This module is bound to a PSL vunits with assert checks
module assert_change_assert (clk, reset_n, start_event, test_expr, window,
                            ignore_new_start, reset_on_new_start, error_on_new_start,
                            xzcheck_enable);
       parameter width = 8;
       parameter num_cks = 2;
       input clk, reset_n, start_event, window, ignore_new_start, reset_on_new_start, error_on_new_start,
             xzcheck_enable;
       input [width-1:0] test_expr;
endmodule

//Module to be replicated for assume checks
//This module is bound to a PSL vunits with assume checks
module assert_change_assume (clk, reset_n, start_event, test_expr, window,
                            ignore_new_start, reset_on_new_start, error_on_new_start,
                            xzcheck_enable);
       parameter width = 8;
       parameter num_cks = 2;
       input clk, reset_n, start_event, window, ignore_new_start, reset_on_new_start, error_on_new_start,
             xzcheck_enable;
       input [width-1:0] test_expr;
endmodule


//Module to be replicated for cover properties
//This module is bound to a PSL vunit with cover properties
module assert_change_cover (clk, reset_n, start_event, window, reset_on_new_start, window_close);
       parameter OVL_COVER_BASIC_ON = 1;
       parameter OVL_COVER_CORNER_ON = 1;
       input clk, reset_n, start_event, window, reset_on_new_start, window_close;
       //wire window_close;//This is for passing the condition while a window is closing
endmodule
