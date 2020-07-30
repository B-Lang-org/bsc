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
  
  localparam values_covered_width = (1<<width);
  localparam stat_cnt_width = 32; 

  integer i;

  reg [width-1:0] r_var;    
  reg clock_after_reset;   

  // Coverage related signals
  reg[stat_cnt_width-1:0]       values_checked;
  reg[stat_cnt_width-1:0]       values_covered;
  reg[stat_cnt_width-1:0]       values_uncovered;
  reg[values_covered_width-1:0] values_covered_bitmap;

  reg[width:0]                  number_of_ones;                       
  reg[width:0]                  number_of_zeros;                      
  reg[is_not_width-1:0]         shifted_is_not;              
  reg[values_covered_width-1:0] is_not_val_bitmap;   
  reg[values_covered_width-1:0] r_is_not_val_bitmap; 
  reg[values_covered_width-1:0] values_cov_bitmap_temp;
  reg[values_covered_width-1:0] values_uncov_bitmap_temp; 
  reg[total_is_not_width-1:0]   new_is_not_temp;

  wire                           all_values_covered;  
  wire[values_covered_width-1:0] current_val_bitmap;
  wire[total_is_not_width-1:0]   is_not_temp;
  wire                           pset_value_coverage_fire;
  wire                           xz_on_var;
  wire                           value_coverage_fire_combo;

`ifdef OVL_SYNTHESIS
`else
   initial begin
     values_checked           = {stat_cnt_width{1'b0}};
     values_covered           = {stat_cnt_width{1'b0}};
     values_uncovered         = {stat_cnt_width{1'b0}};
     values_covered_bitmap    = {values_covered_width{1'b0}};
     number_of_ones           = {(width+1){1'b0}};
     number_of_zeros          = {(width+1){1'b0}};
     is_not_val_bitmap        = {values_covered_width{1'b0}};
     r_is_not_val_bitmap      = {values_covered_width{1'b0}};
     shifted_is_not           = {is_not_width{1'b0}};
     values_cov_bitmap_temp   = {values_covered_width{1'b0}};
     values_uncov_bitmap_temp = {values_covered_width{1'b0}};
     clock_after_reset        = 1'b0;
     r_var                    = {width{1'b0}};
    end
`endif

  // Block for generation of fire and statistics output
  assign pset_value_coverage_fire = (test_expr !== r_var) && (clock_after_reset === 1'b1) ;
  assign xz_on_var = ((test_expr ^ test_expr) !== 0); //Set when one bit in var is x or z

`ifdef OVL_ASSERT_ON
  assign value_coverage_fire_combo = (enable == 1'b1 &&
                      xz_on_var == 1'b0 && 
                      value_coverage == 1'b1 && 
                      pset_value_coverage_fire == 1'b1);
`endif

  assign all_values_covered = (& (values_covered_bitmap |r_is_not_val_bitmap));
  assign current_val_bitmap = (enable === 1'b1) ? (1'b1 << test_expr) :{values_covered_width{1'b0}};

  // The below assignment in done inorder to create an event in case of mti
  // simulator.
  assign is_not_temp = is_not | {total_is_not_width{1'b0}}; 

  always @(current_val_bitmap or values_covered_bitmap or is_not_val_bitmap)
    begin
      number_of_ones  = {(width+1){1'b0}};
      number_of_zeros = {(width+1){1'b0}};

      //values_cov_bitmap_temp is used to evaluate values covered,largest value covered & smallest value covered
      //values_uncov_bitmap_temp is used to evaluate values uncovered ( as it excludes is_not values)

      values_cov_bitmap_temp = values_covered_bitmap | current_val_bitmap ;
      values_uncov_bitmap_temp = ((values_covered_bitmap | current_val_bitmap) | is_not_val_bitmap);

      for (i=0; i<values_covered_width ; i=i+1)
        begin
          if (values_cov_bitmap_temp[i] == 1'b1)
            number_of_ones = number_of_ones + 1;
          else
           if(values_uncov_bitmap_temp[i] == 1'b0)
            begin
              number_of_zeros = number_of_zeros + 1;
            end
        end
    end

  always @(is_not_temp)
    begin
      new_is_not_temp   = is_not_temp;
      shifted_is_not    = new_is_not_temp[is_not_width-1:0];
      is_not_val_bitmap = {values_covered_width{1'b0}};
      for (i=0; i<is_not_count; i=i+1)
        begin
          is_not_val_bitmap = is_not_val_bitmap | (1'b1 << shifted_is_not);
          shifted_is_not    = new_is_not_temp >> is_not_width;
          new_is_not_temp   = new_is_not_temp >> is_not_width;
        end 
    end

  always @(posedge clock)
    begin
      if (`OVL_RESET_SIGNAL != 1'b1)
        begin
      values_checked         <= {stat_cnt_width{1'b0}};
      values_covered         <= {stat_cnt_width{1'b0}};
      values_uncovered       <= {stat_cnt_width{1'b0}};
      values_covered_bitmap  <= {values_covered_width{1'b0}};
          r_is_not_val_bitmap    <= {values_covered_width{1'b0}};
          clock_after_reset      <= 1'b0; 
      r_var                  <= {width{1'b0}};
        end
      else
        begin
          clock_after_reset <= 1'b1;

          if (enable === 1'b1)
            if(xz_on_var === 1'b0)
              begin
                r_var <= test_expr;

        if (pset_value_coverage_fire & enable & ~(&values_checked))
                  values_checked <= values_checked + 1;

                if (~(&values_covered))
                  values_covered  <= number_of_ones; 
                
        if (~(&values_uncovered))
                  values_uncovered<= number_of_zeros;

                values_covered_bitmap  <= values_covered_bitmap | current_val_bitmap;
                r_is_not_val_bitmap    <= is_not_val_bitmap; 
            end 
        end 
    end 
`endif // OVL_SHARED_CODE


`ifdef OVL_ASSERT_ON

  property OVL_VALUE_COVERAGE_CHECK_P;
  @(posedge clock)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
      (value_coverage_fire_combo == 1'b0);
  endproperty

 `ifdef OVL_XCHECK_OFF
    // Do nothing
 `else

  `ifdef OVL_IMPLICIT_XCHECK_OFF
    // Do Nothing
  `else

  property OVL_VALUE_COVERAGE_XZ_IN_TEST_EXPR_P;
  @(posedge clock)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
      (!($isunknown(test_expr)));
  endproperty

  property OVL_VALUE_COVERAGE_XZ_IN_IS_NOT_P;
  @(posedge clock)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
      (!($isunknown(is_not)));
  endproperty

  `endif // OVL_IMPLICIT_XCHECK_OFF
 `endif // OVL_XCHECK_OFF


  generate
    case (property_type)
      `OVL_ASSERT_2STATE,
      `OVL_ASSERT: begin : ovl_assert

           A_OVL_VALUE_COVERAGE_CHECK_P:
           assert property (OVL_VALUE_COVERAGE_CHECK_P)
           else begin
             ovl_error_t(`OVL_FIRE_2STATE,"The value of the variable was covered");
             error_event = 1;
       end  

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
         
     A_OVL_VALUE_COVERAGE_XZ_IN_TEST_EXPR_P:
         assert property (OVL_VALUE_COVERAGE_XZ_IN_TEST_EXPR_P)
         else begin
           ovl_error_t(`OVL_FIRE_XCHECK,"test_expr contains X or Z");
           error_event_xz = 1;
         end

     A_OVL_VALUE_COVERAGE_XZ_IN_IS_NOT_P:
         assert property (OVL_VALUE_COVERAGE_XZ_IN_IS_NOT_P)
         else begin
           ovl_error_t(`OVL_FIRE_XCHECK,"is_not contains X or Z");
           error_event_xz = 1;
         end


  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

      end

      `OVL_ASSUME_2STATE,
      `OVL_ASSUME: begin : ovl_assume
      
         M_OVL_VALUE_COVERAGE_CHECK_P:
         assume property (OVL_VALUE_COVERAGE_CHECK_P);

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else

    M_OVL_VALUE_COVERAGE_XZ_IN_TEST_EXPR_P:
        assume property (OVL_VALUE_COVERAGE_XZ_IN_TEST_EXPR_P);

    M_OVL_VALUE_COVERAGE_XZ_IN_IS_NOT_P:
        assume property (OVL_VALUE_COVERAGE_XZ_IN_IS_NOT_P);
  
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

  generate

    if (coverage_level != `OVL_COVER_NONE) begin : ovl_cover

      if (OVL_COVER_SANITY_ON) begin : ovl_cover_sanity

        cover_values_checked :
          cover property (
            @(posedge clock)
             (`OVL_RESET_SIGNAL != 1'b0) && !$stable(test_expr))
             ovl_cover_t("Test expression changed value");

      end : ovl_cover_sanity

      if (OVL_COVER_STATISTIC_ON) begin : ovl_cover_statistic
        
    cover_computations_checked :
          cover property (
            @(posedge clock)
             (`OVL_RESET_SIGNAL != 1'b0) && !$stable(values_checked))
             ovl_cover_t("Values Checked");
    
    cover_values_covered :
          cover property (
            @(posedge clock)
             (`OVL_RESET_SIGNAL != 1'b0) && !$stable(values_covered))
             ovl_cover_t("Values Covered");
    
    cover_values_uncovered :
          cover property (
            @(posedge clock)
             (`OVL_RESET_SIGNAL != 1'b0) && !$stable(values_uncovered))
             ovl_cover_t("Values Uncovered");

      end : ovl_cover_statistic

      if (OVL_COVER_CORNER_ON) begin : ovl_cover_corner

        cover_all_values_covered:
            cover property (
            @(posedge clock)
             (`OVL_RESET_SIGNAL != 1'b0) && !$stable(all_values_covered))
             ovl_cover_t("All Values Covered");

      end : ovl_cover_corner

    end : ovl_cover

  endgenerate

`endif // OVL_COVER_ON


