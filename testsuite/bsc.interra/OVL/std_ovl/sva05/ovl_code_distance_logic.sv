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

  always @(posedge clk) begin
    if(`OVL_RESET_SIGNAL)
      sva_checker_time_0 <= 1'b0;
    else
      sva_checker_time_0 <= 1'b1;
  end
`endif // OVL_SHARED_CODE

`ifdef OVL_ASSERT_ON

//Checks if code distance is in specified limits

  property OVL_CODE_DISTANCE_P;
  @(posedge clk)
  disable iff(`OVL_RESET_SIGNAL !=1'b1)
  ( !$stable( test_expr1) || sva_checker_time_0) |->
               ((min <= $countones(test_expr1 ^ test_expr2)) &&
                (max >= $countones(test_expr1 ^ test_expr2)));
      endproperty

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
    property OVL_CODE_DISTANCE_XZ_ON_TEST_EXPR_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    (!($isunknown(test_expr1)));
    endproperty

    property OVL_CODE_DISTANCE_XZ_ON_test_expr2_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    (!($isunknown(test_expr2)));
    endproperty
 `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

  generate
    case (property_type)
      `OVL_ASSERT_2STATE,
      `OVL_ASSERT: begin : ovl_assert

       A_OVL_CODE_DISTANCE_P:
          assert property (OVL_CODE_DISTANCE_P)
          else
            begin
              ovl_error_t(`OVL_FIRE_2STATE,"Code distance was not within specified limits");
              error_event = 1;
            end
   `ifdef OVL_XCHECK_OFF
     //Do nothing
   `else
     `ifdef OVL_IMPLICIT_XCHECK_OFF
       //Do nothing
     `else

        A_OVL_CODE_DISTANCE_XZ_ON_TEST_EXPR_P:
        assert property (OVL_CODE_DISTANCE_XZ_ON_TEST_EXPR_P)
        else
          begin
            ovl_error_t(`OVL_FIRE_XCHECK,"test_expr1 contains X or Z");
            error_event_xz = 1;
          end

        A_OVL_CODE_DISTANCE_XZ_ON_test_expr2_P:
        assert property (OVL_CODE_DISTANCE_XZ_ON_test_expr2_P)
        else
        begin
          ovl_error_t(`OVL_FIRE_XCHECK,"test_expr2 contains X or Z");
          error_event_xz = 1;
        end

  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

      end

      `OVL_ASSUME_2STATE,
      `OVL_ASSUME: begin : ovl_assume

       M_OVL_CODE_DISTANCE_P:
          assume property (OVL_CODE_DISTANCE_P);

  `ifdef OVL_XCHECK_OFF
    //Do nothing
  `else
    `ifdef OVL_IMPLICIT_XCHECK_OFF
      //Do nothing
    `else

        M_OVL_CODE_DISTANCE_ON_TEST_EXPR_P:
        assume property (OVL_CODE_DISTANCE_XZ_ON_TEST_EXPR_P);

        M_OVL_CODE_DISTANCE_ON_test_expr2_P:
        assume property (OVL_CODE_DISTANCE_XZ_ON_test_expr2_P);

  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

      end

  `OVL_IGNORE : begin :ovl_ignore
            //do nothing
             end
      default     : initial ovl_error_t(`OVL_FIRE_2STATE,"");
    endcase
  endgenerate

`endif // OVL_ASSERT_ON

`ifdef OVL_COVER_ON

`ifdef OVL_COVERGROUP_ON

   covergroup code_distance_cg(ref integer cnt_ones) @(posedge clk);
        cv :coverpoint cnt_ones iff ((`OVL_RESET_SIGNAL != 1'b0) &&
                ($stable(test_expr1,@ (posedge clk)) || sva_checker_time_0))
                {
            bins observed_code_distance_good[] = {[min:max]};
            bins observed_code_distance_bad = default;}
        option.per_instance = 1;
        option.at_least = 1;
        option.name = "observed_code_distance";
        option.comment = "Bin index is the observed code distance";
      endgroup : code_distance_cg

`endif // `ifdef OVL_COVERGROUP_ON

  generate

    if (coverage_level != `OVL_COVER_NONE) begin : ovl_cover
     if (OVL_COVER_SANITY_ON) begin : ovl_cover_sanity

      cover_test_expr1_changes:
      cover property (@(posedge clk) ( (`OVL_RESET_SIGNAL != 1'b0) &&
                     !$stable(test_expr1) ) )
                       ovl_cover_t("test_expr1_change covered");
     end //sanity coverage

     if (OVL_COVER_CORNER_ON) begin : ovl_cover_corner

      cover_code_distance_at_min:
      cover property (@(posedge clk) ( (`OVL_RESET_SIGNAL != 1'b0) &&
                     (!$stable(test_expr1) || sva_checker_time_0)   &&
                     ($countones(test_expr1^test_expr2) == min) ) )
                     ovl_cover_t("code_distance_at_min covered");


      cover_code_distance_at_max:
      cover property (@(posedge clk) ( (`OVL_RESET_SIGNAL != 1'b0) &&
                     (!$stable(test_expr1) || sva_checker_time_0)   &&
                     ($countones(test_expr1^test_expr2) == max) ) )
                     ovl_cover_t("code_distance_at_max covered");

     end //Corner case Coverage

    if (OVL_COVER_BASIC_ON) begin : ovl_cover_basic

         cover_code_distance_within_limit :
           cover property(@(posedge clk) ((`OVL_RESET_SIGNAL != 1'b0) &&
                        (!$stable(test_expr1) || sva_checker_time_0)   &&
                     ((min < $countones(test_expr1^test_expr2)) &&
                     ($countones(test_expr1^test_expr2) < max)) ) )
                     ovl_cover_t("cover_code_distance_within_limit covered");

`ifdef OVL_COVERGROUP_ON

          integer code_distance_cnt = 0;
          always @ (*)
             code_distance_cnt = $countones(test_expr1^test_expr2);

        code_distance_cg code_distance_cover = new(code_distance_cnt);

`endif //`ifdef OVL_COVERGROUP_ON

     end : ovl_cover_basic

  end: ovl_cover

  endgenerate

`endif
