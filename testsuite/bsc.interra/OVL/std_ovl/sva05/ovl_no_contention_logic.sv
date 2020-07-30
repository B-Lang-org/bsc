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
    if(`OVL_RESET_SIGNAL != 0)
      sva_checker_time_0 <= 1'b0;
    else
      sva_checker_time_0 <= 1'b1;
  end

`ifdef OVL_SYNTHESIS
`else
  generate
    if (max_quiet < 0) begin : max_l_0
          initial $display("Illegal max_quiet parameter value < 0");
    end : max_l_0
    if ((max_quiet !=0) && (max_quiet < min_quiet)) begin : max_ne_0_max_l_min
      initial $display("Illegal max_quiet parameter value < min_quiet");
    end : max_ne_0_max_l_min
    if (min_quiet < 0) begin : min_l_0
      initial $display("Illegal min_quiet parameter value < 0");
    end : min_l_0
  endgenerate
`endif

`endif // OVL_SHARED_CODE

`ifdef OVL_ASSERT_ON

  property OVL_NO_CONTENTION_SINGLE_DRIVER_P;
    @(posedge clk)
      disable iff (`OVL_RESET_SIGNAL != 1'b1)
        ($countones( driver_enables) <= 1);
  endproperty

  property OVL_NO_CONTENTION_NO_XZ_P;
    @(posedge clk)
      disable iff(`OVL_RESET_SIGNAL != 1'b1)
       (driver_enables != 0) |-> !($isunknown(test_expr));
  endproperty

// Properties for the below 4 cases of quiet time:
//   case1 -> min_quiet = 0, max_quiet = 0
//   case2 -> min_quiet = 0, max_quiet > 0
//   case3 -> min_quiet > 0, min_quiet <= max_quiet
//   case4 -> min_quiet > 0, max_quiet = 0

  property OVL_NO_CONTENTION_QUIET_CASE1_P;
    @(posedge clk)
      disable iff(`OVL_RESET_SIGNAL != 1'b1)
        ($countones(driver_enables) == 1);
  endproperty

  property OVL_NO_CONTENTION_QUIET_CASE2_P;
    @(posedge clk)
      disable iff(`OVL_RESET_SIGNAL != 1'b1)
        (($past(driver_enables) != 0 || sva_checker_time_0) &&
         (driver_enables == 0)) |->
             (driver_enables == 0)[*1:max_quiet > 0 ? max_quiet : 1 ]
                ##1 ($countones(driver_enables) == 1);
  endproperty

  property OVL_NO_CONTENTION_QUIET_CASE3_P;
    @(posedge clk)
      disable iff(`OVL_RESET_SIGNAL != 1'b1)
        (($past(driver_enables) != 0 || sva_checker_time_0) &&
               (driver_enables == 0)) |->
        (driver_enables == 0)[*min_quiet:max_quiet < min_quiet ? min_quiet : max_quiet]
          ##1 ($countones(driver_enables) == 1);
  endproperty

  property OVL_NO_CONTENTION_QUIET_CASE4_P;
    @(posedge clk)
      disable iff(`OVL_RESET_SIGNAL != 1'b1)
        (($past(driver_enables) != 0 || sva_checker_time_0) &&
               (driver_enables == 0)) |->
          (driver_enables == 0)[*min_quiet];
  endproperty


`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else

    property OVL_NO_CONTENTION_XZ_ON_DRIVER_ENABLES_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    (!($isunknown(driver_enables)));
    endproperty

  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

  generate
    case (property_type)
      `OVL_ASSERT_2STATE,
      `OVL_ASSERT: begin : ovl_assert

        A_OVL_NO_CONTENTION_SINGLE_DRIVER_P:
        assert property (OVL_NO_CONTENTION_SINGLE_DRIVER_P)
        else begin
          ovl_error_t(`OVL_FIRE_2STATE,"More than 1 drivers are enabled");
          error_event = 1;
        end

        A_OVL_NO_CONTENTION_NO_XZ_P:
        assert property (OVL_NO_CONTENTION_NO_XZ_P)
        else begin
          ovl_error_t(`OVL_FIRE_XCHECK,"when at least 1 driver is enabled bus is going to X or Z");
          error_event = 1;
        end

        if(( min_quiet == 0) && ( max_quiet == 0)) begin : min_e_0_max_e_0
          A_OVL_NO_CONTENTION_QUIET_CASE1_P:
          assert property (OVL_NO_CONTENTION_QUIET_CASE1_P)
          else begin
            ovl_error_t(`OVL_FIRE_2STATE,"test expr (bus) was not quiet minimum for min_quiet and maximum for max_quiet cycles");
            error_event = 1;
          end
        end : min_e_0_max_e_0

        if((min_quiet == 0) && ( max_quiet > 0)) begin : min_e_0_max_g_0
          A_OVL_NO_CONTENTION_QUIET_CASE2_P:
          assert property (OVL_NO_CONTENTION_QUIET_CASE2_P)
          else begin
            ovl_error_t(`OVL_FIRE_2STATE,"test expr (bus) was not quiet minimum for min_quiet and maximum for max_quiet cycles");
            error_event = 1;
          end
        end : min_e_0_max_g_0

        if (( min_quiet > 0) && ( min_quiet <= max_quiet)) begin : min_g_0_min_le_max
          A_OVL_NO_CONTENTION_QUIET_CASE3_P:
          assert property (OVL_NO_CONTENTION_QUIET_CASE3_P)
          else begin
            ovl_error_t(`OVL_FIRE_2STATE,"test expr (bus) was not quiet minimum for min_quiet and maximum for max_quiet cycles");
            error_event = 1;
          end
        end : min_g_0_min_le_max

        if(( min_quiet > 0) && ( max_quiet == 0)) begin : min_g_0_max_e_0
          A_OVL_NO_CONTENTION_QUIET_CASE4_P:
          assert property (OVL_NO_CONTENTION_QUIET_CASE4_P)
          else begin
            ovl_error_t(`OVL_FIRE_2STATE,"test expr (bus) was not quiet minimum for min_quiet and maximum for max_quiet cycles");
            error_event = 1;
          end
        end : min_g_0_max_e_0

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else

        A_OVL_NO_CONTENTION_XZ_ON_DRIVER_ENABLES_P:
        assert property (OVL_NO_CONTENTION_XZ_ON_DRIVER_ENABLES_P)
        else begin
          ovl_error_t(`OVL_FIRE_XCHECK,"driver_enables contains X or Z");
          error_event_xz = 1;
        end

  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

      end

      `OVL_ASSUME_2STATE,
      `OVL_ASSUME: begin : ovl_assume

        M_OVL_NO_CONTENTION_SINGLE_DRIVER_P:
        assume property (OVL_NO_CONTENTION_SINGLE_DRIVER_P);

        M_OVL_NO_CONTENTION_NO_XZ_P:
        assume property (OVL_NO_CONTENTION_NO_XZ_P);

        if(( min_quiet == 0) && ( max_quiet == 0)) begin : min_e_0_max_e_0
          M_OVL_NO_CONTENTION_QUIET_CASE1_P:
          assume property (OVL_NO_CONTENTION_QUIET_CASE1_P);
        end : min_e_0_max_e_0

        if((min_quiet == 0) && ( max_quiet > 0)) begin : min_e_0_max_g_0
          M_OVL_NO_CONTENTION_QUIET_CASE2_P:
          assume property (OVL_NO_CONTENTION_QUIET_CASE2_P);
        end : min_e_0_max_g_0

        if (( min_quiet > 0) && ( min_quiet <= max_quiet)) begin : min_g_0_min_le_max
          M_OVL_NO_CONTENTION_QUIET_CASE3_P:
          assume property (OVL_NO_CONTENTION_QUIET_CASE3_P);
        end : min_g_0_min_le_max

        if(( min_quiet > 0) && ( max_quiet == 0)) begin : min_g_0_max_e_0
          M_OVL_NO_CONTENTION_QUIET_CASE4_P:
          assume property (OVL_NO_CONTENTION_QUIET_CASE4_P);
        end : min_g_0_max_e_0

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else

        M_OVL_NO_CONTENTION_XZ_ON_DRIVER_ENABLES_P:
        assume property (OVL_NO_CONTENTION_XZ_ON_DRIVER_ENABLES_P);

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

`ifdef OVL_COVERGROUP_ON

  localparam d_max_quiet = (( max_quiet < 1) ? (min_quiet == 0 ? 0 :
                                 max_quiet+4095) : max_quiet);

  reg [num_drivers-1:0] past_en_vector;
  integer cnt = 0;

  always @ (posedge clk) begin
    past_en_vector <= driver_enables;
    if(`OVL_RESET_SIGNAL != 1) begin
      cnt <= 0;
    end
    else if((!(|driver_enables)) &&
      ( |past_en_vector || sva_checker_time_0)) begin
      cnt <= 1;
    end
    else begin
      cnt <= cnt+1;
    end
  end

  covergroup quiet_time_cg @(posedge clk);
    coverpoint (|past_en_vector ? 0 : cnt)
      iff((`OVL_RESET_SIGNAL != 0) &&
        (|(driver_enables^past_en_vector))) {
          bins observed_quiet_time_good[] = {[min_quiet:d_max_quiet]};
          bins observed_quiet_time_bad = default;
    }
    option.per_instance = 1;
    option.at_least = 1;
    option.name = "observed_quiet_cycles";
    option.comment = "Bin index is the number of quiet cycles";
  endgroup : quiet_time_cg

`endif // `ifdef OVL_COVERGROUP_ON

  genvar g;

  generate

    if (coverage_level != `OVL_COVER_NONE) begin : ovl_cover

      if (OVL_COVER_SANITY_ON) begin : ovl_cover_sanity

      end : ovl_cover_sanity

      if (OVL_COVER_BASIC_ON) begin : ovl_cover_basic

        for( g = 0; g< num_drivers; g = g+1) begin : driver
            cover_driver_enable:
              cover property(
                @(posedge clk)
                  ((`OVL_RESET_SIGNAL != 0) &&
                    driver_enables[g]));
        end : driver

      end : ovl_cover_basic

      if (OVL_COVER_STATISTIC_ON) begin : ovl_cover_statistic

`ifdef OVL_COVERGROUP_ON
        quiet_time_cg cover_observed_quiet_cycles = new();
`endif

      end : ovl_cover_statistic

      if (OVL_COVER_CORNER_ON) begin : ovl_cover_corner

        if((max_quiet > 0) && (max_quiet >= min_quiet)) begin : max_g_0_max_g_e_min
          cover_quiet_time_equal_to_max_quiet :
            cover property(
              @(posedge clk)
                (`OVL_RESET_SIGNAL != 0) throughout(
                  ( $past(|driver_enables) || sva_checker_time_0) &&
                    ( !(|driver_enables)) ##0
                      ( !(|driver_enables))[*max_quiet]
                        ##1 (|driver_enables)))
            ovl_cover_t("Test expr was stable at value for exactly max clock cycles");
        end : max_g_0_max_g_e_min

        if( min_quiet > 0) begin : min_g_0
          cover_quiet_time_equal_to_min_quiet :
            cover property(
              @(posedge clk)
                (`OVL_RESET_SIGNAL != 0) throughout(
                  ( $past(|driver_enables) || sva_checker_time_0) &&
                    ( !(|driver_enables)) ##0
                      ( !(|driver_enables))[*min_quiet]
                        ##1 (|driver_enables)))
            ovl_cover_t("Test expr was stable at value for exactly min clock cycles");
        end : min_g_0
        if( min_quiet == 0) begin : min_e_0
          cover_quiet_time_equal_to_min_quiet :
            cover property(
              @(posedge clk)
                (`OVL_RESET_SIGNAL != 0) throughout(
                  ( ( !$stable(driver_enables) || sva_checker_time_0) &&
                    ( $past( |driver_enables) || sva_checker_time_0) &&
                    ( |driver_enables))))
            ovl_cover_t("Test expr was stable at value for exactly min clock cycles");
        end : min_e_0

      end : ovl_cover_corner

    end : ovl_cover

  endgenerate

`endif // OVL_COVER_ON
