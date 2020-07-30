// Accellera Standard V2.8.1 Open Verification Library (OVL).
// Accellera Copyright (c) 2005-2014. All rights reserved.

`ifdef OVL_SHARED_CODE

`define log(n) ((n) <= (1<<0) ? 1 :\
                (n) <= (1<<1) ? 1 :\
                (n) <= (1<<2) ? 2 :\
                (n) <= (1<<3) ? 3 :\
                (n) <= (1<<4) ? 4 :\
                (n) <= (1<<5) ? 5 :\
                (n) <= (1<<6) ? 6 :\
                (n) <= (1<<7) ? 7 :\
                (n) <= (1<<8) ? 8 :\
                (n) <= (1<<9) ? 9 :\
                (n) <= (1<<10) ? 10 :\
                (n) <= (1<<11) ? 11 :\
                (n) <= (1<<12) ? 12 :\
                (n) <= (1<<13) ? 13 :\
                (n) <= (1<<14) ? 14 :\
                (n) <= (1<<15) ? 15 :\
                (n) <= (1<<16) ? 16 :\
                (n) <= (1<<17) ? 17 :\
                (n) <= (1<<18) ? 18 :\
                (n) <= (1<<19) ? 19 :\
                (n) <= (1<<20) ? 20 :\
                (n) <= (1<<21) ? 21 :\
                (n) <= (1<<22) ? 22 :\
                (n) <= (1<<23) ? 23 :\
                (n) <= (1<<24) ? 24 :\
                (n) <= (1<<25) ? 25 :\
                (n) <= (1<<26) ? 26 :\
                (n) <= (1<<27) ? 27 :\
                (n) <= (1<<28) ? 28 :\
                (n) <= (1<<29) ? 29 :\
                (n) <= (1<<30) ? 30 :\
                (n) <= (1<<31) ? 31 : 32)

 parameter cnt_reg_width = `log(depth + 1);

 reg [cnt_reg_width-1 : 0] cnt;

`ifdef OVL_SYNTHESIS
`else
 initial cnt = 0;
`endif

  always @(posedge clk) begin
      if (`OVL_RESET_SIGNAL != 1'b0) begin
        if ({push!=0,pop!=0} == 2'b10) begin // push
          if ((cnt + push) <= depth) begin
            cnt <= cnt + push;
          end
        end
        else if ({push!=0,pop!=0} == 2'b01) begin // pop
          if (cnt >= pop) begin
            cnt <= cnt - pop;
          end
        end
        else if ({push!=0,pop!=0} == 2'b11) begin // push & pop
          if (!simultaneous_push_pop) begin
            //ILLEGAL PUSH AND POP, do not update local count
          end
          else begin
            if ((cnt + push - pop) > depth) begin
              //OVERFLOW, do not update local count
            end
            else if ((cnt + push) < pop) begin
              //UNDERFLOW, do not update local count
            end
            else begin
              cnt <= cnt + push - pop;
            end
          end
        end
      end
      else begin
        cnt <= 0;
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
         assert_fifo_index_assert #(
                       .depth(depth),
                       .push_width(push_width),
                       .pop_width(pop_width),
                       .simultaneous_push_pop(simultaneous_push_pop),
                       .cnt_reg_width(cnt_reg_width))
                assert_fifo_index_assert (
                       .clk(clk),
                       .reset_n(`OVL_RESET_SIGNAL),
                       .push(push),
                       .pop(pop),
                       .cnt(cnt),
                       .xzcheck_enable(xzcheck_enable));
                  end
     `OVL_ASSUME_2STATE,
     `OVL_ASSUME: begin: assume_checks
         assert_fifo_index_assume #(
                       .depth(depth),
                       .push_width(push_width),
                       .pop_width(pop_width),
                       .simultaneous_push_pop(simultaneous_push_pop),
                       .cnt_reg_width(cnt_reg_width))
                assert_fifo_index_assume (
                       .clk(clk),
                       .reset_n(`OVL_RESET_SIGNAL),
                       .push(push),
                       .pop(pop),
                       .cnt(cnt),
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
          assert_fifo_index_cover #(
                       .depth(depth),
                       .push_width(push_width),
                       .pop_width(pop_width),
                       .simultaneous_push_pop(simultaneous_push_pop),
                       .cnt_reg_width(cnt_reg_width),
                       .OVL_COVER_BASIC_ON(OVL_COVER_BASIC_ON),
                       .OVL_COVER_CORNER_ON(OVL_COVER_CORNER_ON))
                assert_fifo_index_cover (
                       .clk(clk),
                       .reset_n(`OVL_RESET_SIGNAL),
                       .push(push),
                       .pop(pop),
                       .cnt(cnt));
   end
 endgenerate
`endif

`endmodule //Required to pair up with already used "`module" in file assert_fifo_index.vlib

//Module to be replicated for assert checks
//This module is bound to a PSL vunits with assert checks
module assert_fifo_index_assert (clk, reset_n, push, pop, cnt, xzcheck_enable);
       parameter depth=1;
       parameter push_width = 1;
       parameter pop_width = 1;
       parameter simultaneous_push_pop = 1;
       parameter cnt_reg_width = 1;
       input clk, reset_n;
       input [push_width-1:0] push;
       input [pop_width-1:0] pop;
       input [cnt_reg_width-1:0] cnt;
       input xzcheck_enable;

//Any required modeling layer code for asserted properties here

endmodule

//Module to be replicated for assume checks
//This module is bound to a PSL vunits with assume checks
module assert_fifo_index_assume (clk, reset_n, push, pop, cnt, xzcheck_enable);
       parameter depth=1;
       parameter push_width = 1;
       parameter pop_width = 1;
       parameter simultaneous_push_pop = 1;
       parameter cnt_reg_width = 1;
       input clk, reset_n;
       input [push_width-1:0] push;
       input [pop_width-1:0] pop;
       input [cnt_reg_width-1:0] cnt;
       input xzcheck_enable;

//Any required modeling layer code for assumed properties here

endmodule


//Module to be replicated for cover properties
//This module is bound to a PSL vunit with cover properties
module assert_fifo_index_cover (clk, reset_n, push, pop, cnt);
       parameter depth=1;
       parameter push_width = 1;
       parameter pop_width = 1;
       parameter simultaneous_push_pop = 1;
       parameter cnt_reg_width = 1;
       parameter OVL_COVER_BASIC_ON = 1;
       parameter OVL_COVER_CORNER_ON = 1;
       input clk, reset_n;
       input [push_width-1:0] push;
       input [pop_width-1:0] pop;
       input [cnt_reg_width-1:0] cnt;

//Any only coverage related modeling layer code for properties here

endmodule
