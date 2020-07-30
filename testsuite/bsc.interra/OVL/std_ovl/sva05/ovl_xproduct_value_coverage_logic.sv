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

  localparam var1_max       = (max1 ? max1 : {width1{1'b1}});
  localparam var2_max       = (max2 ? max2 : {width2{1'b1}});
  localparam bit_vec1_width = (val1_count > 0) ? val1_count : (var1_max - min1 + 1);
  localparam bit_vec2_width = (val2_count > 0) ? val2_count : (var2_max - min2 + 1);
  localparam bitmap_width   = bit_vec1_width*bit_vec2_width;
  localparam stat_cnt_width = 32;

  reg                         forced_first_cov;
  reg [width1-1:0]            old_var1; 
  reg [width2-1:0]            old_var2; 
  reg [stat_cnt_width-1:0]    values_checked;
  reg [bitmap_width-1:0]      coverage_matrix_bitmap;
  reg [bitmap_width-1:0]      tmp_coverage_matrix_bitmap;
  reg [bit_vec1_width-1:0]    var1_bit_vec;
  reg [bit_vec2_width-1:0]    var2_bit_vec;
  reg [val1_width_internal:0] local_val1; 
  reg [val2_width_internal:0] local_val2; 

  wire matrix_covered;
  wire xpd_covered_fire_combo;

  integer i,j;

  assign matrix_covered = (coverage_matrix_bitmap == {bitmap_width{1'b1}});

  assign xpd_covered_fire_combo = (enable === 1'b1) && (coverage_check > 0) && 
                                  ((test_expr1 !== old_var1) || (test_expr2 !== old_var2) || (!forced_first_cov)) &&
                  ((test_expr1^test_expr1) === 1'b0) && ((test_expr2^test_expr2) === 1'b0) &&
                                  (((cur_xpd_bitmap(var1_bit_vec,var2_bit_vec)| coverage_matrix_bitmap)) === {bitmap_width{1'b1}});
 
`ifdef OVL_SYNTHESIS
`else

   initial begin
     forced_first_cov = 1'b0;
     old_var1 = {width1{1'b0}};
     old_var2 = {width1{1'b0}};
     values_checked = 64'h0;
     coverage_matrix_bitmap = {bitmap_width{1'b0}};
     tmp_coverage_matrix_bitmap = {bitmap_width{1'b0}};
   end
`endif

  always @(posedge clock) begin
    if (`OVL_RESET_SIGNAL !== 1'b1) begin
      forced_first_cov           <= 1'b0;
      old_var1                   <= {width1{1'b0}};
      old_var2                   <= {width1{1'b0}};
      tmp_coverage_matrix_bitmap <= {bitmap_width{1'b0}};
      coverage_matrix_bitmap     <= {bitmap_width{1'b0}};
      values_checked             <= {stat_cnt_width{1'b0}};
    end
    else if ((enable !== 1'b1) || ((test_expr1^test_expr1) !== 1'b0) || ((test_expr2^test_expr2) !== 1'b0)) begin
      forced_first_cov <= 1'b0;
    end 
    else begin
      forced_first_cov <= 1'b1;
      old_var1 <= test_expr1;
      old_var2 <= test_expr2;
      
      if ((test_expr1 !== old_var1) || (test_expr2 !== old_var2) || (!forced_first_cov))
        tmp_coverage_matrix_bitmap = cur_xpd_bitmap(var1_bit_vec,var2_bit_vec) | coverage_matrix_bitmap;
      
      if (((test_expr1 !== old_var1) || (test_expr2 !== old_var2) || !forced_first_cov))  begin
        coverage_matrix_bitmap <= tmp_coverage_matrix_bitmap;
        values_checked <= values_checked + 1'b1;
      end
    end
  end

  always @ (test_expr1, val1) begin
    var1_bit_vec = 'h0;
    local_val1 = val1;
    if (val1_count > 0) begin
      for (i=0; i<val1_count; i=i+1) begin
        if (test_expr1 === local_val1[val1_width-1:0]) begin
          var1_bit_vec[i] = 1'b1;
        end
        local_val1 = local_val1 >> val1_width;
      end
    end
    else begin
      if ((test_expr1 >= min1) && (test_expr1 <= var1_max)) begin
         var1_bit_vec[test_expr1-min1] = 1'b1;
      end
    end
  end

  always @ (test_expr2, val2) begin
    var2_bit_vec = 'h0;
    local_val2 = val2;
    if (val2_count > 0) begin
      for (j=0; j<val2_count; j=j+1) begin
        if (test_expr2 === local_val2[val2_width-1:0]) begin
          var2_bit_vec[j] = 1'b1;
        end
        local_val2 = local_val2 >> val2_width;
      end
    end
    else begin
      if ((test_expr2 >= min2) && (test_expr2 <= var2_max)) begin
         var2_bit_vec[test_expr2-min2] = 1'b1;
      end
    end
  end

  function [bitmap_width-1:0] cur_xpd_bitmap;
    input [bit_vec1_width-1:0] v1;
    input [bit_vec2_width-1:0] v2;
    integer i;
    begin
      cur_xpd_bitmap = {bitmap_width{1'b0}};
      for (i=0; i<bit_vec1_width; i = i+1) begin
    cur_xpd_bitmap = cur_xpd_bitmap >> bit_vec2_width;
        cur_xpd_bitmap[bitmap_width-1:bitmap_width-bit_vec2_width] = {bit_vec2_width{v1[i]}} & v2;
      end
    end
  endfunction

`endif // OVL_SHARED_CODE

`ifdef OVL_ASSERT_ON

  property OVL_XPRODUCT_VALUE_COVERAGE_CHECKED_P;
  @(posedge clock)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
      (xpd_covered_fire_combo === 1'b0);
  endproperty

 `ifdef OVL_XCHECK_OFF
    // Do nothing
 `else

  `ifdef OVL_IMPLICIT_XCHECK_OFF
    // Do Nothing
  `else

  property OVL_XPRODUCT_VALUE_COVERAGE_XZ_IN_TEST_EXPR1_P;
  @(posedge clock)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
      (!($isunknown(test_expr1)));
  endproperty

  property OVL_XPRODUCT_VALUE_COVERAGE_XZ_IN_TEST_EXPR2_P;
  @(posedge clock)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
      (!($isunknown(test_expr2)));
  endproperty

  property OVL_XPRODUCT_VALUE_COVERAGE_XZ_IN_VAL1_P;
  @(posedge clock)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
      (!($isunknown(val1)));
  endproperty

  property OVL_XPRODUCT_VALUE_COVERAGE_XZ_IN_VAL2_P;
  @(posedge clock)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
      (!($isunknown(val2)));
  endproperty

  `endif // OVL_IMPLICIT_XCHECK_OFF
 `endif // OVL_XCHECK_OFF


  generate
    case (property_type)
      `OVL_ASSERT_2STATE,
      `OVL_ASSERT: begin : ovl_assert

           A_OVL_XPRODUCT_VALUE_COVERAGE_CHECKED_P:
           assert property (OVL_XPRODUCT_VALUE_COVERAGE_CHECKED_P)
           else begin
             ovl_error_t(`OVL_FIRE_2STATE,"All bits of the coverage matrix were covered");
             error_event = 1;
           end  

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
         
     A_OVL_XPRODUCT_VALUE_COVERAGE_XZ_IN_TEST_EXPR1_P:
         assert property (OVL_XPRODUCT_VALUE_COVERAGE_XZ_IN_TEST_EXPR1_P)
         else begin
           ovl_error_t(`OVL_FIRE_XCHECK,"test_expr1 contains X or Z");
           error_event_xz = 1;
         end

     A_OVL_XPRODUCT_VALUE_COVERAGE_XZ_IN_TEST_EXPR2_P:
         assert property (OVL_XPRODUCT_VALUE_COVERAGE_XZ_IN_TEST_EXPR2_P)
         else begin
           ovl_error_t(`OVL_FIRE_XCHECK,"test_expr2 contains X or Z");
           error_event_xz = 1;
         end

     A_OVL_XPRODUCT_VALUE_COVERAGE_XZ_IN_VAL1_P:
         assert property (OVL_XPRODUCT_VALUE_COVERAGE_XZ_IN_VAL1_P)
         else begin
           ovl_error_t(`OVL_FIRE_XCHECK,"val1 contains X or Z");
           error_event_xz = 1;
         end

     A_OVL_XPRODUCT_VALUE_COVERAGE_XZ_IN_VAL2_P:
         assert property (OVL_XPRODUCT_VALUE_COVERAGE_XZ_IN_VAL2_P)
         else begin
           ovl_error_t(`OVL_FIRE_XCHECK,"val2 contains X or Z");
           error_event_xz = 1;
         end

  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

      end

      `OVL_ASSUME_2STATE,
      `OVL_ASSUME: begin : ovl_assume
      
         M_OVL_XPRODUCT_VALUE_COVERAGE_CHECKED_P:
         assume property (OVL_XPRODUCT_VALUE_COVERAGE_CHECKED_P);

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else

    M_OVL_XPRODUCT_VALUE_COVERAGE_XZ_IN_TEST_EXPR1_P:
        assume property (OVL_XPRODUCT_VALUE_COVERAGE_XZ_IN_TEST_EXPR1_P);

    M_OVL_XPRODUCT_VALUE_COVERAGE_XZ_IN_TEST_EXPR2_P:
        assume property (OVL_XPRODUCT_VALUE_COVERAGE_XZ_IN_TEST_EXPR2_P);
    
    M_OVL_XPRODUCT_VALUE_COVERAGE_XZ_IN_VAL1_P:
        assume property (OVL_XPRODUCT_VALUE_COVERAGE_XZ_IN_VAL1_P);
    
    M_OVL_XPRODUCT_VALUE_COVERAGE_XZ_IN_VAL2_P:
        assume property (OVL_XPRODUCT_VALUE_COVERAGE_XZ_IN_VAL2_P);
  
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

        cover_test_expr1_checked :
          cover property (
            @(posedge clock)
             (`OVL_RESET_SIGNAL != 1'b0) && !$stable(test_expr1))
             ovl_cover_t("Test expression 1 changed value");
        
    cover_test_expr2_checked :
          cover property (
            @(posedge clock)
             (`OVL_RESET_SIGNAL != 1'b0) && !$stable(test_expr2))
             ovl_cover_t("Test expression 2 changed value");

      end : ovl_cover_sanity

      if (OVL_COVER_STATISTIC_ON) begin : ovl_cover_statistic
        
    cover_value_checked :
          cover property (
            @(posedge clock)
             (`OVL_RESET_SIGNAL != 1'b0) && !$stable(values_checked))
             ovl_cover_t("Values Checked");
    
      end : ovl_cover_statistic

      if (OVL_COVER_CORNER_ON) begin : ovl_cover_corner

        cover_matrix_covered :
            cover property (
            @(posedge clock)
             (`OVL_RESET_SIGNAL != 1'b0) && !$stable(matrix_covered))
             ovl_cover_t("Matrix Covered");

      end : ovl_cover_corner

    end : ovl_cover

  endgenerate

`endif // OVL_COVER_ON


