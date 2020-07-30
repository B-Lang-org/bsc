// Accellera Standard V2.8.1 Open Verification Library (OVL).
// Accellera Copyright (c) 2005-2014. All rights reserved.



`ifdef OVL_ASSERT_ON

wire end_of_simulation;
`ifdef OVL_END_OF_SIMULATION
assign end_of_simulation = `OVL_END_OF_SIMULATION;
`else
assign end_of_simulation = 1'b0;
`endif

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
         assert_quiescent_state_assert #(
                       .width(width) )
                assert_quiescent_state_assert (
                       .clk(clk),
                       .reset_n(`OVL_RESET_SIGNAL),
                       .state_expr(state_expr),
                       .check_value(check_value),
                       .sample_event(sample_event),
                       .end_of_simulation (end_of_simulation) ,
                       .xzcheck_enable(xzcheck_enable));
                  end
     `OVL_ASSUME_2STATE,
     `OVL_ASSUME: begin: assume_checks
         assert_quiescent_state_assume #(
                       .width(width) )
                assert_quiescent_state_assume (
                       .clk(clk),
                       .reset_n(`OVL_RESET_SIGNAL),
                       .state_expr(state_expr),
                       .check_value(check_value),
                       .sample_event(sample_event),
                       .end_of_simulation (end_of_simulation) ,
                       .xzcheck_enable(xzcheck_enable));
                  end
     `OVL_IGNORE: begin: ovl_ignore
                    //do nothing
                  end
     default: initial ovl_error_t(`OVL_FIRE_2STATE,"");
   endcase
 endgenerate

`endif

`endmodule //Required to pair up with already used "`module" in file assert_quiescent_state.vlib

//Module to be replicated for assert checks
//This module is bound to a PSL vunits with assert checks
module assert_quiescent_state_assert (clk, reset_n, state_expr, check_value, sample_event, end_of_simulation, xzcheck_enable);
       parameter width = 8;
       input clk, reset_n, sample_event;
       input [width-1:0]  state_expr, check_value;
       input end_of_simulation;
input xzcheck_enable;
endmodule

//Module to be replicated for assume checks
//This module is bound to a PSL vunits with assume checks
module assert_quiescent_state_assume (clk, reset_n, state_expr, check_value, sample_event, end_of_simulation, xzcheck_enable);
       parameter width = 8;
       input clk, reset_n, sample_event;
       input [width-1:0] state_expr, check_value;
       input end_of_simulation;
       input xzcheck_enable;
endmodule

