// Accellera Standard V2.8.1 Open Verification Library (OVL).
// Accellera Copyright (c) 2005-2014. All rights reserved.

  wire ignore_new_start   = (action_on_new_start == `OVL_IGNORE_NEW_START);
  wire reset_on_new_start = (action_on_new_start == `OVL_RESET_ON_NEW_START);
  wire error_on_new_start = (action_on_new_start == `OVL_ERROR_ON_NEW_START);


`ifdef OVL_ASSERT_ON

  integer ii;
  reg win;
  reg r_start_event;

  always @(posedge clk) begin
    r_start_event <= start_event;
  end

  always @(posedge clk) begin
    if (`OVL_RESET_SIGNAL != 1'b1) begin
      ii <= 0;
      win <= 0;
    end
    else begin
      if (max_cks > 0) begin
        case (win)
          0: begin
            if (r_start_event == 1'b0 && start_event == 1'b1 &&
                (test_expr != 1'b1)) begin
              win <= 1'b1;
              ii <= max_cks;
            end
          end
          1: begin
            if (r_start_event == 1'b0 && start_event == 1'b1 &&
                action_on_new_start == `OVL_RESET_ON_NEW_START &&
                test_expr != 1'b1) begin
              ii <= max_cks;
            end
            else if (ii <= 1 || test_expr == 1'b1) begin
              win <= 1'b0;
            end
            else begin
              ii <= ii -1;
            end
          end
        endcase
      end
      else if (min_cks > 0) begin
        case (win)
          0: begin
            if (r_start_event == 1'b0 && start_event == 1'b1 &&
                (test_expr != 1'b1)) begin
              win <= 1'b1;
              ii <= min_cks;
            end
          end
          1: begin
            if (r_start_event == 1'b0 && start_event == 1'b1 &&
                action_on_new_start == `OVL_RESET_ON_NEW_START &&
                test_expr != 1'b1) begin
              ii <= min_cks;
            end
            else if (ii <= 1 || test_expr == 1'b1) begin
              win <= 1'b0;
            end
            else begin
              ii <= ii -1;
            end
          end
        endcase
      end
    end
  end

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
         assert_frame_assert #(
                       .min_cks(min_cks),
                       .max_cks(max_cks))
                assert_frame_assert (
                       .clk(clk),
                       .reset_n(`OVL_RESET_SIGNAL),
                       .start_event(start_event),
                       .test_expr(test_expr),
                       .win(win),
                       .ignore_new_start(ignore_new_start),
                       .reset_on_new_start(reset_on_new_start),
                       .error_on_new_start(error_on_new_start),
                       .xzcheck_enable(xzcheck_enable));
                  end
     `OVL_ASSUME_2STATE,
     `OVL_ASSUME: begin: assume_checks
         assert_frame_assume #(
                       .min_cks(min_cks),
                       .max_cks(max_cks))
                assert_frame_assume (
                       .clk(clk),
                       .reset_n(`OVL_RESET_SIGNAL),
                       .start_event(start_event),
                       .test_expr(test_expr),
                       .win(win),
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
          assert_frame_cover #(
                       .OVL_COVER_BASIC_ON(OVL_COVER_BASIC_ON))
                assert_frame_cover (
                       .clk(clk),
                       .reset_n(`OVL_RESET_SIGNAL),
                       .start_event(start_event));
   end
 endgenerate
`endif

`endmodule //Required to pair up with already used "`module" in file assert_frame.vlib

//Module to be replicated for assert checks
//This module is bound to a PSL vunits with assert checks
module assert_frame_assert (clk, reset_n, start_event, test_expr, win,
                            ignore_new_start, reset_on_new_start, error_on_new_start,
                            xzcheck_enable);
       parameter min_cks = 1;
       parameter max_cks = 2;
       input clk, reset_n, start_event, test_expr, win,
             ignore_new_start, reset_on_new_start, error_on_new_start,
             xzcheck_enable;
endmodule

//Module to be replicated for assume checks
//This module is bound to a PSL vunits with assume checks
module assert_frame_assume (clk, reset_n, start_event, test_expr, win,
                            ignore_new_start, reset_on_new_start, error_on_new_start,
                            xzcheck_enable);
       parameter min_cks = 1;
       parameter max_cks = 2;
       input clk, reset_n, start_event, test_expr, win,
             ignore_new_start, reset_on_new_start, error_on_new_start,
             xzcheck_enable;
endmodule


//Module to be replicated for cover properties
//This module is bound to a PSL vunit with cover properties
module assert_frame_cover (clk, reset_n, start_event);
       parameter OVL_COVER_BASIC_ON = 1;
       input clk, reset_n, start_event;
endmodule
