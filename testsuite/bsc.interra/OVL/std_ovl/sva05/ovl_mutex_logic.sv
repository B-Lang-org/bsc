// Accellera Standard V2.8.1 Open Verification Library (OVL).
// Accellera Copyright (c) 2005-2014. All rights reserved.


  bit error_event, error_event_xz;

`ifdef OVL_ASSERT_ON

  always @(posedge clk)
  begin
    error_event = 0;
    error_event_xz = 0;
  end

`endif // OVL_ASSERT_ON

`ifdef OVL_REVISIT // Tied low in V2.3 (in top-level file)
  `ifdef OVL_ASSERT_ON
    assign fire[0] = error_event;
    assign fire[1] = error_event_xz;
  `else
    assign fire[0] = 1'b0;
    assign fire[1] = 1'b0;
  `endif // OVL_ASSERT_ON

  `ifdef OVL_COVER_ON
    assign fire[2] = 1'b0;
  `else
    assign fire[2] = 1'b0;
  `endif // OVL_COVER_ON
`endif // OVL_REVISIT

`ifdef OVL_SHARED_CODE

  wire [width-1 : 0] bit_vector;

  assign bit_vector = (invert_mode == 0) ? test_expr : ~test_expr;

`endif // OVL_SHARED_CODE

`ifdef OVL_ASSERT_ON

  property OVL_MUTEX_P;
  @(posedge clk)
  disable iff(`OVL_RESET_SIGNAL != 1'b1)
  (!($countones(bit_vector) > 1));
  endproperty

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else

    property OVL_MUTEX_XZ_ON_TEST_EXPR_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    (!($isunknown(test_expr)));
    endproperty

  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

  generate
    case (property_type)
      `OVL_ASSERT_2STATE,
      `OVL_ASSERT: begin : ovl_assert

          A_OVL_MUTEX_P:
          assert property (OVL_MUTEX_P)
          else begin
            ovl_error_t(`OVL_FIRE_2STATE,"Expression's bits are not mutually exclusive");
            error_event = 1;
          end

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else

        A_OVL_MUTEX_XZ_ON_TEST_EXPR_P:
        assert property (OVL_MUTEX_XZ_ON_TEST_EXPR_P)
        else begin
          ovl_error_t(`OVL_FIRE_XCHECK,"test_expr contains X or Z");
          error_event_xz = 1;
        end

  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

      end

      `OVL_ASSUME_2STATE,
      `OVL_ASSUME: begin : ovl_assume

          M_OVL_MUTEX_P:
          assume property (OVL_MUTEX_P);

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else

        M_OVL_MUTEX_XZ_ON_TEST_EXPR_P:
        assume property (OVL_MUTEX_XZ_ON_TEST_EXPR_P);

  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

      end

      `OVL_IGNORE : begin : ovl_ignore
        // do nothing;
      end
      default     : initial ovl_error_t(`OVL_FIRE_2STATE,"");
    endcase
  endgenerate

`endif // OVL_ASSERT_ON


`ifdef OVL_COVER_ON

  reg [width-1:0] mutex_bitmap, mutex_bitmap_tmp;

  genvar g;

  generate

    if (coverage_level != `OVL_COVER_NONE) begin : ovl_cover

      if (OVL_COVER_SANITY_ON) begin : ovl_cover_sanity

        cover_values_checked :
          cover property(
            @(posedge clk)
             (`OVL_RESET_SIGNAL != 1'b0) && !$stable(bit_vector))
             ovl_cover_t("Test expression changed value");

      end : ovl_cover_sanity

      if (OVL_COVER_BASIC_ON) begin : ovl_cover_basic

      end : ovl_cover_basic

      if (OVL_COVER_STATISTIC_ON) begin : ovl_cover_statistic

        cover_mutex_bitmap:
          cover property(
            @(posedge clk)
             (`OVL_RESET_SIGNAL != 1'b0) && ($countones(bit_vector) == 1) &&
             ((mutex_bitmap | bit_vector) != mutex_bitmap)) begin
               ovl_cover_t ("New mutex bit covered. TRUE bits of mutex_bitmap are the covered mutex bits");
               mutex_bitmap_tmp = bit_vector;
             end

      end : ovl_cover_statistic


      if (OVL_COVER_CORNER_ON) begin : ovl_cover_corner

        cover_all_mutexes_covered:
          cover property(
             @(posedge clk)
             (`OVL_RESET_SIGNAL != 1'b0) &&
             $rose($countones(mutex_bitmap) == width))
             ovl_cover_t ("All mutex bits covered");

        cover_no_mutex_bits :
          cover property(
            @(posedge clk)
             (`OVL_RESET_SIGNAL != 1'b0) && (bit_vector == {width{1'b0}}) )
             ovl_cover_t("None of the bits of test expr is asserted (invert_mode=0) or deasserted (invert_mode=1)");

      end : ovl_cover_corner

    end : ovl_cover

  endgenerate

 always @ (posedge clk)
   if (`OVL_RESET_SIGNAL == 1'b0) begin
    mutex_bitmap <= {width{1'b0}};
    mutex_bitmap_tmp <= {width{1'b0}};
   end
   else
    mutex_bitmap <= mutex_bitmap | mutex_bitmap_tmp;

`endif // OVL_COVER_ON

