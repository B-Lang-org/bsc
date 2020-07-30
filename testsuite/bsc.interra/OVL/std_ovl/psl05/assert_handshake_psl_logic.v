// Accellera Standard V2.8.1 Open Verification Library (OVL).
// Accellera Copyright (c) 2005-2014. All rights reserved.



`ifdef OVL_ASSERT_ON

 reg first_req;
 wire xzcheck_enable;

  always @ (posedge clk) begin
    if (`OVL_RESET_SIGNAL != 1'b0) begin
      if((first_req ^ first_req) == 1'b0) begin
        if (req)
          first_req <= 1'b1;
        end
        else begin
          first_req <= 1'b0;
        end
      end
    else
      first_req <= 1'b0;
  end

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
                   assert_handshake_assert #(
                       .min_ack_cycle(min_ack_cycle),
                       .max_ack_cycle(max_ack_cycle),
                       .req_drop(req_drop),
                       .deassert_count(deassert_count),
                       .max_ack_length(max_ack_length))
                   assert_handshake_assert (
                       .clk(clk),
                       .reset_n(`OVL_RESET_SIGNAL),
                       .req(req),
                       .ack(ack),
                       .first_req(first_req),
                       .xzcheck_enable(xzcheck_enable));
                  end
     `OVL_ASSUME_2STATE,
     `OVL_ASSUME: begin: assume_checks
                   assert_handshake_assume #(
                       .min_ack_cycle(min_ack_cycle),
                       .max_ack_cycle(max_ack_cycle),
                       .req_drop(req_drop),
                       .deassert_count(deassert_count),
                       .max_ack_length(max_ack_length))
                   assert_handshake_assume (
                       .clk(clk),
                       .reset_n(`OVL_RESET_SIGNAL),
                       .req(req),
                       .ack(ack),
                       .first_req(first_req),
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
          assert_handshake_cover #(
                       .OVL_COVER_BASIC_ON(OVL_COVER_BASIC_ON))
          assert_handshake_cover (
                       .clk(clk),
                       .reset_n(`OVL_RESET_SIGNAL),
                       .req(req),
                       .ack(ack));
   end
 endgenerate
`endif

`endmodule //Required to pair up with already used "`module" in file assert_handshake.vlib

//Module to be replicated for assert checks
//This module is bound to a PSL vunits with assert checks
module assert_handshake_assert (clk, reset_n, req, ack, first_req, xzcheck_enable);
       parameter min_ack_cycle = 0;
       parameter max_ack_cycle = 0;
       parameter req_drop = 0;
       parameter deassert_count = 0;
       parameter max_ack_length = 0;
       input clk, reset_n, req, ack, first_req, xzcheck_enable;
endmodule

//Module to be replicated for assume checks
//This module is bound to a PSL vunits with assume checks
module assert_handshake_assume (clk, reset_n, req, ack, first_req, xzcheck_enable);
       parameter min_ack_cycle = 0;
       parameter max_ack_cycle = 0;
       parameter req_drop = 0;
       parameter deassert_count = 0;
       parameter max_ack_length = 0;
       input clk, reset_n, req, ack, first_req, xzcheck_enable;
endmodule

//Module to be replicated for cover properties
//This module is bound to a PSL vunit with cover properties
module assert_handshake_cover (clk, reset_n, req, ack);
       parameter OVL_COVER_BASIC_ON = 1;
       input clk, reset_n, req, ack;
endmodule
