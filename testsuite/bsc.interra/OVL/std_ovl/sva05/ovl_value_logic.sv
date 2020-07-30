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

  reg sva_checker_time_0 = 1'b1;

  always @ (posedge clk) begin
    if(`OVL_RESET_SIGNAL != 1'b0)
      sva_checker_time_0 <= 1'b0;
    else
      sva_checker_time_0 <= 1'b1;
  end

  reg [num_values-1 : 0] sva_value = {num_values{1'b0}};
  integer i, j;

  always @(*) begin
    if (disallow == 1'b0) begin
      for (i = 0; i < num_values; i=i+1) begin
        sva_value[i] = (test_expr == vals[(width*(i+1))-1 -: width]);
      end
    end
    else begin
      for (j = 0; j < num_values; j=j+1) begin
        sva_value[j] = (test_expr != vals[(width*(j+1))-1 -: width]);
      end
    end
  end

`endif // OVL_SHARED_CODE

`ifdef OVL_ASSERT_ON

  property OVL_VALUE_VALUE_CHECK_P;
    @(posedge clk)
      disable iff(`OVL_RESET_SIGNAL != 1'b1)
      (disallow == 1'b0) |-> |(sva_value);
  endproperty

  property OVL_VALUE_INVERT_VALUE_CHECK_P;
    @(posedge clk)
      disable iff(`OVL_RESET_SIGNAL != 1'b1)
      (disallow == 1'b1) |-> &(sva_value);
  endproperty


`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else

    property OVL_VALUE_XZ_ON_TEST_EXPR_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    (!($isunknown(test_expr)));
    endproperty

    property OVL_VALUE_XZ_ON_VALS_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    (!($isunknown(vals)));
    endproperty

    property OVL_VALUE_XZ_ON_INVERT_MODE_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    (!($isunknown(disallow)));
    endproperty

  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

  generate
    case (property_type)
      `OVL_ASSERT_2STATE,
      `OVL_ASSERT: begin : ovl_assert

          A_OVL_VALUE_VALUE_CHECK_P:
          assert property (OVL_VALUE_VALUE_CHECK_P)
          else begin
            ovl_error_t(`OVL_FIRE_2STATE,"test expr is not having value equal to one of the specified values");
            error_event = 1;
          end

          A_OVL_VALUE_INVERT_VALUE_CHECK_P:
          assert property (OVL_VALUE_INVERT_VALUE_CHECK_P)
          else begin
            ovl_error_t(`OVL_FIRE_2STATE,"test expr is having value equal to one of the specified values");
            error_event = 1;
          end

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else

        A_OVL_VALUE_XZ_ON_TEST_EXPR_P:
        assert property (OVL_VALUE_XZ_ON_TEST_EXPR_P)
        else begin
          ovl_error_t(`OVL_FIRE_XCHECK,"test_expr contains X or Z");
          error_event_xz = 1;
        end

        A_OVL_VALUE_XZ_ON_VALS_P:
        assert property (OVL_VALUE_XZ_ON_VALS_P)
        else begin
          ovl_error_t(`OVL_FIRE_XCHECK,"vals contains X or Z");
          error_event_xz = 1;
        end

        A_OVL_VALUE_XZ_ON_INVERT_MODE_P:
        assert property (OVL_VALUE_XZ_ON_INVERT_MODE_P)
        else begin
          ovl_error_t(`OVL_FIRE_XCHECK,"disallow contains X or Z");
          error_event_xz = 1;
        end

  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

      end

      `OVL_ASSUME_2STATE,
      `OVL_ASSUME: begin : ovl_assume

          M_OVL_VALUE_VALUE_CHECK_P:
          assume property (OVL_VALUE_VALUE_CHECK_P);

          M_OVL_VALUE_INVERT_VALUE_CHECK_P:
          assume property (OVL_VALUE_INVERT_VALUE_CHECK_P);

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else

        M_OVL_VALUE_XZ_ON_TEST_EXPR_P:
        assume property (OVL_VALUE_XZ_ON_TEST_EXPR_P);

        M_OVL_VALUE_XZ_ON_VALS_P:
        assume property (OVL_VALUE_XZ_ON_VALS_P);

        M_OVL_VALUE_XZ_ON_INVERT_MODE_P:
        assume property (OVL_VALUE_XZ_ON_INVERT_MODE_P);

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

  genvar k;

  generate

    if (coverage_level != `OVL_COVER_NONE) begin : ovl_cover

      if (OVL_COVER_SANITY_ON) begin : ovl_cover_sanity

    cover_values_checked:
          cover property(
            @(posedge clk) (
              (`OVL_RESET_SIGNAL != 1'b0) && !$stable(test_expr)))
        ovl_cover_t("test expression loaded a new value");

      end : ovl_cover_sanity

      if (OVL_COVER_BASIC_ON) begin : ovl_cover_basic

        cover_values_covered_mode0:
          cover property(
            @(posedge clk)
              (`OVL_RESET_SIGNAL != 1'b0) && !disallow throughout(
               |sva_value))
        ovl_cover_t("test expression changed to one of the specified vals");

        cover_values_covered_mode1:
          cover property(
            @(posedge clk)
              (`OVL_RESET_SIGNAL != 1'b0) && disallow throughout(
               &sva_value))
        ovl_cover_t("test expression changed to one of the value other than the specified vals");

        for( k = 0; k < num_values; k=k+1) begin : value
          cover_each_value_covered:
            cover property(
              @(posedge clk)
                (`OVL_RESET_SIGNAL != 1'b0 ) && !disallow throughout (
                  ( !$stable( test_expr) || sva_checker_time_0) &&
                    ( test_expr == vals[width*(k+1)-1 : width*k])));
        end : value

      end : ovl_cover_basic

      if (OVL_COVER_STATISTIC_ON) begin : ovl_cover_statistic

      end : ovl_cover_statistic

      if (OVL_COVER_CORNER_ON) begin : ovl_cover_corner

      end : ovl_cover_corner

    end : ovl_cover

  endgenerate

`endif // OVL_COVER_ON
