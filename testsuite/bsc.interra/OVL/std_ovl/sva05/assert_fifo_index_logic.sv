// Accellera Standard V2.8.1 Open Verification Library (OVL).
// Accellera Copyright (c) 2005-2014. All rights reserved.

`ifdef OVL_SHARED_CODE

 integer cnt;

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
            //ILLEGAL PUSH AND POP
          end
          else begin
            if ((cnt + push - pop) > depth) begin
              //OVERFLOW"
            end
            else if ((cnt + push) < pop) begin
              //UNDERFLOW
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

  property ASSERT_FIFO_INDEX_OVERFLOW_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  push && !(!simultaneous_push_pop && push && pop) |-> ((cnt + push - pop) <= depth);
  endproperty

  property ASSERT_FIFO_INDEX_UNDERFLOW_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  (pop && !(!simultaneous_push_pop && push && pop) && (push == 0 || (((cnt + push - pop) <= depth)))) |-> ((cnt + push) >= pop);
  endproperty

  property ASSERT_FIFO_INDEX_ILLEGAL_PUSH_POP_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  !(push && pop);
  endproperty


`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
  property ASSERT_FIFO_INDEX_XZ_ON_PUSH_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  (!($isunknown(push)));
  endproperty

  property ASSERT_FIFO_INDEX_XZ_ON_POP_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  (!($isunknown(pop)));
  endproperty

  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

  generate

    case (property_type)
      `OVL_ASSERT_2STATE,
      `OVL_ASSERT: begin : ovl_assert

        A_ASSERT_FIFO_INDEX_OVERFLOW_P:
        assert property (ASSERT_FIFO_INDEX_OVERFLOW_P)
        else ovl_error_t(`OVL_FIRE_2STATE,"Fifo overflow detected");

        A_ASSERT_FIFO_INDEX_UNDERFLOW_P:
        assert property (ASSERT_FIFO_INDEX_UNDERFLOW_P)
        else ovl_error_t(`OVL_FIRE_2STATE,"Fifo underflow detected");


`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
        A_ASSERT_FIFO_INDEX_XZ_ON_PUSH_P:
        assert property (ASSERT_FIFO_INDEX_XZ_ON_PUSH_P)
        else ovl_error_t(`OVL_FIRE_XCHECK,"push contains X or Z");

        A_ASSERT_FIFO_INDEX_XZ_ON_POP_P:
        assert property (ASSERT_FIFO_INDEX_XZ_ON_POP_P)
        else ovl_error_t(`OVL_FIRE_XCHECK,"pop contains X or Z");
  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF


        if (!simultaneous_push_pop) begin : a_assert_fifo_index_illegal_push_pop
          A_ASSERT_FIFO_INDEX_ILLEGAL_PUSH_POP_P:
          assert property (ASSERT_FIFO_INDEX_ILLEGAL_PUSH_POP_P)
          else ovl_error_t(`OVL_FIRE_2STATE,"Illegal simultaneous push pop detected");
        end
      end
      `OVL_ASSUME_2STATE,
      `OVL_ASSUME: begin : ovl_assume

        M_ASSERT_FIFO_INDEX_OVERFLOW_P:
        assume property (ASSERT_FIFO_INDEX_OVERFLOW_P);

        M_ASSERT_FIFO_INDEX_UNDERFLOW_P:
        assume property (ASSERT_FIFO_INDEX_UNDERFLOW_P);


`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
        M_ASSERT_FIFO_INDEX_XZ_ON_PUSH_P:
        assume property (ASSERT_FIFO_INDEX_XZ_ON_PUSH_P);

        M_ASSERT_FIFO_INDEX_XZ_ON_POP_P:
        assume property (ASSERT_FIFO_INDEX_XZ_ON_POP_P);
  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF


        if (!simultaneous_push_pop) begin : m_assert_fifo_index_illegal_push_pop
          M_ASSERT_FIFO_INDEX_ILLEGAL_PUSH_POP_P:
          assume property (ASSERT_FIFO_INDEX_ILLEGAL_PUSH_POP_P);
        end
      end
      `OVL_IGNORE : begin : ovl_ignore
        // do nothing;
      end
      default     : initial ovl_error_t(`OVL_FIRE_2STATE,"");
    endcase

  endgenerate

`endif // OVL_ASSERT_ON

`ifdef OVL_COVER_ON

generate

 if (coverage_level != `OVL_COVER_NONE) begin : ovl_cover
  if (OVL_COVER_BASIC_ON) begin : ovl_cover_basic

   cover_fifo_push:
   cover property ( @(posedge clk) ((`OVL_RESET_SIGNAL != 1'b0) &&
      push && pop == 0))
      ovl_cover_t("fifo_push covered");

   cover_fifo_pop:
   cover property ( @(posedge clk) ((`OVL_RESET_SIGNAL != 1'b0) &&
      pop && push == 0))
      ovl_cover_t("fifo_pop covered");
  end //basic coverage

  if (OVL_COVER_CORNER_ON) begin : ovl_cover_corner

   cover_fifo_full:
   cover property ( @(posedge clk) ((`OVL_RESET_SIGNAL != 1'b0) &&
      // case where only push is true and fifo goes to full
      (((push !=0) && (cnt +push == depth) && (pop ==0)) ||

      // case with simultaneous push and pop and fifo goes to full
      ((pop != 0) && (push != 0) && ((cnt - pop + push) == depth) &&
      (simultaneous_push_pop)))
      ) )
    ovl_cover_t("fifo_full covered");

   cover_fifo_empty:
   cover property ( @(posedge clk) ((`OVL_RESET_SIGNAL != 1'b0) &&
      // case where only pop is true and fifo goes to empty
      (((pop != 0) && (push == 0) && ((cnt - pop) == 0)) ||

      // case with simultaneous push and pop and fifo goes to empty
      ((pop != 0) && (push != 0) && ((cnt - pop + push) == 0) &&
      (simultaneous_push_pop)))
      ) )
      ovl_cover_t("fifo_empty covered");

   cover_fifo_simultaneous_push_pop:
   cover property ( @(posedge clk) ((`OVL_RESET_SIGNAL != 1'b0) && push && pop))
      ovl_cover_t("fifo_simultaneous_push_pop covered");
  end //corner coverage

 end // OVL_COVER_NONE

endgenerate

`endif // OVL_COVER_ON
