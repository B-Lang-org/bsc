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
  
  localparam width3         = (width1 * width2); 
  localparam func_w1        = (width1 == 1) ? 1 : width1-1; 
  localparam width4         = (width1 == 1) ? 1 : (func_w1)*(func_w1); 
  localparam bitmap_width   = (test_expr2_enable == 1) ? width3 : width4; 
  localparam stat_cnt_width = 32;
  
  reg                      forced_first_cov;
  reg [width1-1:0]         old_test_expr1; 
  reg [width2-1:0]         old_test_expr2; 
  reg [stat_cnt_width-1:0] values_checked;
  reg [bitmap_width-1:0]   coverage_matrix_bitmap;
  reg [bitmap_width-1:0]   tmp_coverage_matrix_bitmap;
  
  wire matrix_covered;
  wire xpd_covered_fire_combo;


  assign matrix_covered = (coverage_matrix_bitmap == {bitmap_width{1'b1}});

  assign xpd_covered_fire_combo = (enable === 1'b1) && 
                                  (coverage_check === 1'b1) && 
                                  ((((test_expr2_enable ? cur_xpd_bitmap(test_expr1,test_expr2) : cur_cov_bmap(test_expr1)) | coverage_matrix_bitmap)) === {bitmap_width{1'b1}});

`ifdef OVL_SYNTHESIS
`else
   initial begin
    forced_first_cov           = 1'b0;
    old_test_expr1             = {width1{1'b0}};
    old_test_expr2             = {width2{1'b0}};
    values_checked             = {stat_cnt_width{1'b0}};
    coverage_matrix_bitmap     = {bitmap_width{1'b0}};
    tmp_coverage_matrix_bitmap = {bitmap_width{1'b0}};
    end
`endif

  always @(posedge clock) begin
    if (`OVL_RESET_SIGNAL !== 1'b1) begin
      forced_first_cov           <= 1'b0;
      old_test_expr1             <= {width1{1'b0}};
      old_test_expr2             <= {width2{1'b0}};
      coverage_matrix_bitmap     <= {bitmap_width{1'b0}};
      tmp_coverage_matrix_bitmap <= {bitmap_width{1'b0}};
    end
    else if ((enable !== 1'b1) || ((test_expr1^test_expr1) !== 1'b0) || ((test_expr2^test_expr2) !== 1'b0)) begin
      forced_first_cov <= 1'b0;
    end 
    else begin
      forced_first_cov <= 1'b1;
      old_test_expr1 <= test_expr1;
      old_test_expr2 <= test_expr2;
      tmp_coverage_matrix_bitmap = 
        (test_expr2_enable ? cur_xpd_bitmap(test_expr1,test_expr2) : cur_cov_bmap(test_expr1)) | coverage_matrix_bitmap;
      coverage_matrix_bitmap <= tmp_coverage_matrix_bitmap;
      if (((test_expr1 !== old_test_expr1) || (test_expr2 !== old_test_expr2) || !forced_first_cov))  begin
        values_checked <= values_checked + 1'b1;
      end
    end
  end

  function [width3-1:0] cur_xpd_bitmap;
    input [width1-1:0] v1;
    input [width2-1:0] v2;
    integer i;
    begin
      cur_xpd_bitmap = {width3{1'b0}};
      for (i=0; i<width1; i = i+1) begin
    cur_xpd_bitmap = cur_xpd_bitmap >> width2;
        cur_xpd_bitmap[width3-1:width3-width2] = {width2{v1[i]}} & v2;
      end
    end
  endfunction

  function [width4-1:0] cur_cov_bmap;
    input [width1-1:0] v1;
    integer i;
    reg [func_w1-1:0] mask;
    reg [func_w1-1:0] a;
    reg [func_w1-1:0] b;
    begin
      cur_cov_bmap = {width4{1'b0}};
      for (i=0; i<func_w1; i = i+1) begin
        mask = ~({func_w1{1'b1}} >> i);
        a = {func_w1{v1[width1-1-i]}} | mask;
        b = v1[func_w1-1:0] | mask;
        cur_cov_bmap = cur_cov_bmap << func_w1;
        cur_cov_bmap[func_w1-1:0] = a & b;
      end
    end
  endfunction

`endif // OVL_SHARED_CODE

`ifdef OVL_ASSERT_ON

  property OVL_XPRODUCT_BIT_COVERAGE_CHECKED_P;
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

  property OVL_XPRODUCT_BIT_COVERAGE_XZ_IN_TEST_EXPR1_P;
  @(posedge clock)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
      (!($isunknown(test_expr1)));
  endproperty

  property OVL_XPRODUCT_BIT_COVERAGE_XZ_IN_TEST_EXPR2_P;
  @(posedge clock)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
      (!($isunknown(test_expr2)));
  endproperty

  `endif // OVL_IMPLICIT_XCHECK_OFF
 `endif // OVL_XCHECK_OFF


  generate
    case (property_type)
      `OVL_ASSERT_2STATE,
      `OVL_ASSERT: begin : ovl_assert

           A_OVL_XPRODUCT_BIT_COVERAGE_CHECKED_P:
           assert property (OVL_XPRODUCT_BIT_COVERAGE_CHECKED_P)
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
         
     A_OVL_XPRODUCT_BIT_COVERAGE_XZ_IN_TEST_EXPR1_P:
         assert property (OVL_XPRODUCT_BIT_COVERAGE_XZ_IN_TEST_EXPR1_P)
         else begin
           ovl_error_t(`OVL_FIRE_XCHECK,"test_expr1 contains X or Z");
           error_event_xz = 1;
         end

     A_OVL_XPRODUCT_BIT_COVERAGE_XZ_IN_TEST_EXPR2_P:
         assert property (OVL_XPRODUCT_BIT_COVERAGE_XZ_IN_TEST_EXPR2_P)
         else begin
           ovl_error_t(`OVL_FIRE_XCHECK,"test_expr2 contains X or Z");
           error_event_xz = 1;
         end


  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

      end

      `OVL_ASSUME_2STATE,
      `OVL_ASSUME: begin : ovl_assume
      
         M_OVL_XPRODUCT_BIT_COVERAGE_CHECKED_P:
         assume property (OVL_XPRODUCT_BIT_COVERAGE_CHECKED_P);

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else

    M_OVL_XPRODUCT_BIT_COVERAGE_XZ_IN_TEST_EXPR1_P:
        assume property (OVL_XPRODUCT_BIT_COVERAGE_XZ_IN_TEST_EXPR1_P);

    M_OVL_XPRODUCT_BIT_COVERAGE_XZ_IN_TEST_EXPR2_P:
        assume property (OVL_XPRODUCT_BIT_COVERAGE_XZ_IN_TEST_EXPR2_P);
  
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
        
    if (test_expr2_enable == 1) begin : cover_test_expr2_enable
    cover_test_expr2_checked :
          cover property (
            @(posedge clock)
             (`OVL_RESET_SIGNAL != 1'b0) && (test_expr2_enable === 1) && !$stable(test_expr2))
             ovl_cover_t("Test expression 2 changed value");
    end       

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

