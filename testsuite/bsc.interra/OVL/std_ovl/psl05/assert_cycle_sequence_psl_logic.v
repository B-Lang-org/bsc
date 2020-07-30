// Accellera Standard V2.8.1 Open Verification Library (OVL).
// Accellera Copyright (c) 2005-2014. All rights reserved.

`ifdef OVL_SHARED_CODE

  parameter NUM_CKS_1 = (num_cks-1);
  parameter NUM_CKS_2 = (NUM_CKS_1 > 0) ? (NUM_CKS_1 - 1) : 0;

  reg [NUM_CKS_1:0]  seq_queue;

`ifdef OVL_SYNTHESIS
`else
  initial begin
    seq_queue = {num_cks{1'b0}};
  end
`endif

  always @ (posedge clk) begin
    if (`OVL_RESET_SIGNAL != 1'b1) begin
      seq_queue <= {num_cks{1'b0}};
    end
    else begin
      seq_queue[NUM_CKS_1] <= (necessary_condition == `OVL_TRIGGER_ON_FIRST_NOPIPE) ?
                              (~(|seq_queue[NUM_CKS_1:1])) && event_sequence[NUM_CKS_1] : event_sequence[NUM_CKS_1];
      seq_queue[NUM_CKS_2:0] <= (seq_queue >> 1) & event_sequence[NUM_CKS_2:0];
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
                   assert_cycle_sequence_assert #(
                       .num_cks(num_cks),
                       .necessary_condition(necessary_condition))
                   assert_cycle_sequence_assert (
                       .clk(clk),
                       .reset_n(`OVL_RESET_SIGNAL),
                       .event_sequence(event_sequence),
                       .seq_queue(seq_queue),
                       .xzcheck_enable(xzcheck_enable));
                  end
     `OVL_ASSUME_2STATE,
     `OVL_ASSUME: begin: assume_checks
                   assert_cycle_sequence_assume #(
                       .num_cks(num_cks),
                       .necessary_condition(necessary_condition))
                   assert_cycle_sequence_assume (
                       .clk(clk),
                       .reset_n(`OVL_RESET_SIGNAL),
                       .event_sequence(event_sequence),
                       .seq_queue(seq_queue),
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
    assert_cycle_sequence_cover #(
                       .num_cks(num_cks),
                       .necessary_condition(necessary_condition),
                       .OVL_COVER_BASIC_ON(OVL_COVER_BASIC_ON))
    assert_cycle_sequence_cover (
                       .clk(clk),
                       .reset_n(`OVL_RESET_SIGNAL),
                       .event_sequence(event_sequence),
                       .seq_queue(seq_queue));

   end
 endgenerate
`endif

`endmodule //Required to pair up with already used "`module" in file assert_cycle_sequence.vlib

//Module to be replicated for assert checks
//This module is bound to a PSL vunits with assert checks
module assert_cycle_sequence_assert (clk, reset_n, event_sequence, seq_queue, xzcheck_enable);
       parameter num_cks = 2;
       parameter necessary_condition = 0;
       input clk, reset_n;
       input [num_cks-1:0] event_sequence, seq_queue;
       input xzcheck_enable;
endmodule

//Module to be replicated for assume checks
//This module is bound to a PSL vunits with assume checks
module assert_cycle_sequence_assume (clk, reset_n, event_sequence, seq_queue, xzcheck_enable);
       parameter num_cks = 2;
       parameter necessary_condition = 0;
       input clk, reset_n;
       input [num_cks-1:0] event_sequence, seq_queue;
       input xzcheck_enable;
endmodule


//Module to be replicated for cover properties
//This module is bound to a PSL vunit with cover properties
module assert_cycle_sequence_cover (clk, reset_n, event_sequence, seq_queue);
       parameter num_cks = 4;
       parameter necessary_condition = 0;
       parameter OVL_COVER_BASIC_ON = 1;
       input clk, reset_n;
       input [num_cks-1:0] event_sequence, seq_queue;
endmodule
