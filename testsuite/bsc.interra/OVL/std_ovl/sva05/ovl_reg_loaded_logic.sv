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

   reg[width-1:0] sva_v_reg_src_expr      = {width{1'b0}};
   reg            past_start_event         = 1'b0;
   reg            sva_checker_time_0 = 1'b1;
   integer        cnt                = 0;

`ifdef OVL_SYNTHESIS
`else
 initial begin
   if( ( start_count > end_count) && ( end_count != 0)) begin
      $display("Illegal end_count value specified ( end_count < start_count)");
   end
 end
`endif

 localparam d_end_count = end_count == 0 ? start_count+4095 : end_count;

  always @ (posedge clk) begin
    if(`OVL_RESET_SIGNAL != 1'b0) begin
       sva_v_reg_src_expr      <= (start_event && !past_start_event) ? src_expr : sva_v_reg_src_expr;
       past_start_event         <=  start_event;
       sva_checker_time_0 <= 1'b0;
    end
    else begin
       sva_v_reg_src_expr      <= {width{1'b0}};
       past_start_event         <= 1'b0;
       sva_checker_time_0 <= 1'b1;
    end
    if( (`OVL_RESET_SIGNAL != 1'b1) ||
        ( (end_event || (dest_expr == sva_v_reg_src_expr)) && ( cnt > 0 ))) begin
        cnt <= 0;
    end    
    else if( ( ( start_event && !past_start_event) ||
           ( start_event && sva_checker_time_0)) && cnt==0) begin
        cnt <= 1;
    end
    else if( cnt > 0) begin
        cnt <= cnt + 1;
    end
 end

`endif // OVL_SHARED_CODE

`ifdef OVL_ASSERT_ON

// Properties for reg_loaded
   property OVL_REG_LOADED_CASE1_P; //start_count <= end_count
     @(posedge clk)
        disable iff(`OVL_RESET_SIGNAL != 1'b1)
          ( ( start_event && sva_checker_time_0) || $rose( start_event)) |->
          ( !end_event) throughout
           ##[start_count:d_end_count] (dest_expr == sva_v_reg_src_expr);
   endproperty

   property OVL_REG_LOADED_CASE2_P; //start_count > end_count
     @(posedge clk)
        disable iff(`OVL_RESET_SIGNAL != 1'b1)
          ( $rose( start_event) || ( start_event && sva_checker_time_0)) |->
          ( !end_event) throughout
           ##[start_count:$] (dest_expr == sva_v_reg_src_expr);
   endproperty

// Properties for XZ checking:
//   XZ checking on start_event signal
//   XZ checking on end_event signal
//   XZ checking on src_expr input
//   XZ checking on dest_expr input

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else

    property OVL_REG_LOADED_XZ_ON_START_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    (!($isunknown(start_event)));
    endproperty

    property OVL_REG_LOADED_XZ_ON_STOP_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    (!($isunknown(end_event)));
    endproperty

    property OVL_REG_LOADED_XZ_ON_SRC_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    (!($isunknown(src_expr)));
    endproperty

    property OVL_REG_LOADED_XZ_ON_DST_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    (!($isunknown(dest_expr)));
    endproperty

  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

 generate

    case (property_type)
      `OVL_ASSERT_2STATE,
      `OVL_ASSERT: begin : ovl_assert

        if( start_count <= end_count) begin : ovl_case1
          A_OVL_REG_LOADED_CASE1_P:
            assert property (OVL_REG_LOADED_CASE1_P)
              else begin
                ovl_error_t(`OVL_FIRE_2STATE,"Destination expression did not equal the value of the source expression in the specified time window");
                error_event = 1;
              end
        end
        else begin :ovl_case2
          A_OVL_REG_LOADED_CASE2_P:
            assert property (OVL_REG_LOADED_CASE2_P)
              else begin
                ovl_error_t(`OVL_FIRE_2STATE,"Destination expression did not equal the value of the source expression in the time window that ended when end_event asserted");
                error_event = 1;
              end
        end

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else

        A_OVL_REG_LOADED_XZ_ON_START_P:
        assert property (OVL_REG_LOADED_XZ_ON_START_P)
        else begin
          ovl_error_t(`OVL_FIRE_XCHECK,"start_event contains X or Z");
          error_event_xz = 1;
        end

        A_OVL_REG_LOADED_XZ_ON_STOP_P:
        assert property (OVL_REG_LOADED_XZ_ON_STOP_P)
        else begin
          ovl_error_t(`OVL_FIRE_XCHECK,"end_event contains X or Z");
          error_event_xz = 1;
        end

        A_OVL_REG_LOADED_XZ_ON_SRC_P:
        assert property (OVL_REG_LOADED_XZ_ON_SRC_P)
        else begin
          ovl_error_t(`OVL_FIRE_XCHECK,"src_expr contains X or Z");
          error_event_xz = 1;
        end

        A_OVL_REG_LOADED_XZ_ON_DST_P:
        assert property (OVL_REG_LOADED_XZ_ON_DST_P)
        else begin
          ovl_error_t(`OVL_FIRE_XCHECK,"dest_expr contains X or Z");
          error_event_xz = 1;
        end

  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

      end

      `OVL_ASSUME_2STATE,
      `OVL_ASSUME: begin : ovl_assume

        if( start_count <= end_count) begin
         M_OVL_REG_LOADED_CASE1_P:
          assume property (OVL_REG_LOADED_CASE1_P);
        end
    else begin
         M_OVL_REG_LOADED_CASE2_P:
          assume property (OVL_REG_LOADED_CASE2_P);
        end

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else

        M_OVL_REG_LOADED_XZ_ON_START_P:
        assume property (OVL_REG_LOADED_XZ_ON_START_P);

        M_OVL_REG_LOADED_XZ_ON_STOP_P:
        assume property (OVL_REG_LOADED_XZ_ON_STOP_P);

        M_OVL_REG_LOADED_XZ_ON_SRC_P:
        assume property (OVL_REG_LOADED_XZ_ON_SRC_P);

        M_OVL_REG_LOADED_XZ_ON_DST_P:
        assume property (OVL_REG_LOADED_XZ_ON_DST_P);

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

  covergroup load_time_cg @(posedge clk);
    coverpoint cnt
      iff((`OVL_RESET_SIGNAL != 1'b0) &&
          (end_event) && (dest_expr == sva_v_reg_src_expr) && ( cnt > 0)) {
             bins observed_load_time_good[] = {[start_count:d_end_count]};
             bins observed_load_time_bad    = default;
           }
           option.per_instance = 1;
           option.at_least = 1;
           option.name = "observed_dest_expr_reg_load_time";
           option.comment = "Bin index is the observed load time of dest_expr reg";
  endgroup : load_time_cg

`endif

  generate

    if (coverage_level != `OVL_COVER_NONE) begin : ovl_cover

      if (OVL_COVER_SANITY_ON) begin : ovl_cover_sanity

        cover_no_of_times_start_event_asserted:
           cover property(
              @(posedge clk)
                (`OVL_RESET_SIGNAL != 1'b0) throughout
        ( $rose( start_event) || ( start_event && sva_checker_time_0)))
             ovl_cover_t("Rising edge of Start signal arrived");

      end : ovl_cover_sanity

      if (OVL_COVER_BASIC_ON) begin : ovl_cover_basic

        if( start_count <= end_count) begin : ovl_cover_case1
      cover_reg_loaded :
            cover property(
              @(posedge clk)
                ((`OVL_RESET_SIGNAL != 1'b0) && (!end_event))
                 throughout (
                ($rose( start_event) || ( start_event && sva_checker_time_0))
                 ##[start_count:end_count] ( dest_expr == sva_v_reg_src_expr)))
             ovl_cover_t("Dst reg loaded with Src reg value");
         end
        else begin :ovl_cover_case_2
        cover_reg_loaded :
            cover property(
              @(posedge clk)
                ((`OVL_RESET_SIGNAL != 1'b0) && (!end_event))
                 throughout (
                ( $rose( start_event) || ( start_event && sva_checker_time_0)) ##[start_count:$]
                ( dest_expr == sva_v_reg_src_expr)))
             ovl_cover_t("Dst reg loaded with Src reg value");
           end

        if( ( end_count >= start_count) && ( end_count > 0)) begin : ovl_cover_case2
           cover_no_of_times_end_event_happened_at_or_prior_to_end_count :
             cover property(
              @(posedge clk)
                (`OVL_RESET_SIGNAL != 1'b0) throughout
                (( $rose( start_event) ||( start_event && sva_checker_time_0))
             ##[0:end_count] end_event))
             ovl_cover_t("Stop asserted before end_count has expired");

       cover_no_of_times_no_end_event_happened_till_end_count :
              cover property(
               @(posedge clk)
                (`OVL_RESET_SIGNAL != 1'b0) ##1
                (((`OVL_RESET_SIGNAL != 1'b0) && (!end_event))
          throughout (
                  ( $rose( start_event) || ( start_event && sva_checker_time_0))
           ##end_count 1'b1)))
             ovl_cover_t("No Stop asserted before end_count has expired");
    end
      end : ovl_cover_basic

      if (OVL_COVER_STATISTIC_ON) begin : ovl_cover_statistic

`ifdef OVL_COVERGROUP_ON
         load_time_cg load_time_cover = new();
`endif    

      end : ovl_cover_statistic

      if (OVL_COVER_CORNER_ON) begin : ovl_cover_corner

        if( ( start_count <= end_count) && ( end_count > 0)) begin : ovl_cover_case3
      cover_data_transfer_exactly_at_end_count :
            cover property(
              @(posedge clk)
                ((`OVL_RESET_SIGNAL != 1'b0) && (!end_event))
                 throughout (
                ( $rose( start_event) ||( start_event && sva_checker_time_0)) ##start_count
                ( dest_expr != sva_v_reg_src_expr)[*(end_count-start_count)] ##1
                ( dest_expr == sva_v_reg_src_expr)))
             ovl_cover_t("Dst reg loaded with Src reg value exactly at end_count");
        end

        cover_data_transfer_exactly_at_start_count :
          cover property(
             @(posedge clk)
                ((`OVL_RESET_SIGNAL != 1'b0) && (!end_event))
                 throughout (
                ( $rose( start_event) ||( start_event && sva_checker_time_0))  ##start_count
                ( dest_expr == sva_v_reg_src_expr)))
             ovl_cover_t("Dst reg loaded with Src reg value exactly at start_count");

      end : ovl_cover_corner

    end : ovl_cover

  endgenerate

`endif // OVL_COVER_ON
