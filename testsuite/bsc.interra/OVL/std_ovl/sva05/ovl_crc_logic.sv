// Accellera Standard V2.8.1 Open Verification Library (OVL).
// Accellera Copyright (c) 2005-2014. All rights reserved.


  bit error_event, error_event_xz;
  bit xz_detected_in_valid;

`ifdef OVL_ASSERT_ON

  always @(posedge clk)
  begin
    error_event = 0;
    error_event_xz = 0;
  end

  always @(posedge clk)
  begin
	xz_detected_in_valid = 0;
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
 
  // Internal parameter declarations
  localparam crc_poly_specified = (polynomial == 0) ? 0 : 1; 
  
  localparam latch_crc_specified = (crc_latch_enable == 0) ? 0 : 1; 
  
  localparam crc_computation_width_internal = (data_width > 0) ? data_width : width; 
  
  localparam crc_comp_counter_width = log2(crc_computation_width_internal); 
  
  localparam in_crc_specified = (crc_enable == 0) ? 0 : 1; 
  
  localparam int_initial_crc_value = (initial_value == 0) ? 0 : (initial_value + 1);
  
  localparam crc_comp_count = (crc_computation_width_internal == width);  

  localparam stat_cnt_width = 32;
  
  localparam crc5 = 5'h05;
  
  localparam crc7 = 7'h09;

  localparam crc16 = 16'h1021;

  localparam crc32 = 32'h04c11db7;
  
  localparam std_poly_width = (standard_polynomial === 1) ? 5  :
                              (standard_polynomial === 2) ? 7  :
                              (standard_polynomial === 3) ? 16 :
                              (standard_polynomial === 4) ? 32 : 
                  (standard_polynomial === 5) ? 64 : 1;
  
  localparam temp_crc_width = (crc_poly_specified) ? crc_width : std_poly_width;

  localparam computed_crc_width = (in_crc_specified === 1'b0) ? width-1 : temp_crc_width-1 ;

  localparam acc_reg_width = (crc_comp_count === 1) ? width-1 : (crc_computation_width_internal-width-1);

  localparam temp_crc_a = (temp_crc_width < width) ? temp_crc_width : width;

  // Register declarations
  reg [temp_crc_width-1:0]                   r_combo_crc; 
  reg [stat_cnt_width-1:0]                   total_crc_computations;
  reg [stat_cnt_width-1:0]                   cycles_checked;
  reg [temp_crc_width-1:0]                   latch_crc_reg;
  reg [crc_comp_counter_width:0]             crc_comp_width_counter;
  reg [temp_crc_width-1:0]                   temp_expected_crc_value;
  reg [temp_crc_width-1:0]                   temp_latch_crc_value;
  reg                                        r_compare_crc_enable;
  reg                                        r_compute_crc_flag;
  reg [crc_computation_width_internal-1:0]   temp_accumulation_reg;
  reg [crc_computation_width_internal-1:0]   swap_data;
  reg [crc_computation_width_internal-1:0]   acc_reg;
  reg                                        temp_compute_crc_flag;

  // Wire declaration for combinatorial fire signal
  wire                                       start_crc;
  wire                                       latch_crc;
  wire                                       compare_crc_enable;
  wire                                       in_data_valid;
  wire                                       compute_crc;
  wire                                       not_compute_crc;
  wire                                       compute_crc_flag;
  wire                                       crc_fire_combo;
  wire [temp_crc_width-1:0]                  combo_crc; 
  wire [temp_crc_width-1:0]                  final_crc; 
  wire [crc_computation_width_internal-1:0]  accumulation_reg;
  wire [temp_crc_width-1:0]                  crc_function_poly_in;
  wire [temp_crc_width-1:0]                  initial_crc_value;   
  wire [temp_crc_width-1:0]                  new_crc_value;       
  wire [computed_crc_width:0]                latched_crc_value;
  wire [computed_crc_width:0]                calculated_crc_value;
  wire [computed_crc_width:0]                computed_crc_value;
  wire [computed_crc_width:0]                temp_expected_crc;
  wire [computed_crc_width:0]                temp_latched_crc;
  wire [computed_crc_width:0]                final_crc_value;
  wire [computed_crc_width:0]                in_crc_value;
  wire [crc_computation_width_internal-1:0]  final_data;
  wire                                       temp_latch_crc;
  wire                                       crc_check_fire_combo;

  integer bit_loop_count;

  //******************************************************************************
  // Function to compute CRC
  //******************************************************************************

  function [temp_crc_width-1:0] expected_crc;

    input[temp_crc_width-1:0] new_crc; 
    input[crc_computation_width_internal-1:0] data; 
    input[temp_crc_width-1:0] crc_poly;             

    integer i;
    reg[temp_crc_width-1:0] crc; 
    reg temp;                   
    begin
      crc = new_crc;
      for(i=0;i<crc_computation_width_internal;i=i+1)
        begin
          temp = ((crc >> temp_crc_width-1) ^ (data >> crc_computation_width_internal-1));
          crc = crc << 1;
          crc = temp ? crc ^ crc_poly : crc;
          data = data << 1;
        end
        expected_crc = crc;
    end
  endfunction 
  
  //************************************************************************************
  
  // Signal assignments
  assign temp_latch_crc = (latch_crc_specified ? crc_latch : 1'b0);
  
  assign start_crc = (initialize === 1'b1);

  assign latch_crc = (temp_latch_crc === 1'b1);
  
  assign compare_crc_enable = (compare === 1'b1);

  assign in_data_valid = (valid === 1'b1);

  assign compute_crc_flag = (crc_comp_count === 1) ? 1'b1 : 
                            (r_compute_crc_flag !== 1'b1 &&
                            (crc_comp_width_counter === width) &&
                             !(start_crc || latch_crc));
 
  assign compute_crc = (start_crc || latch_crc || in_data_valid);

  // Standard crc5 polynomial x^5 + x^2 + 1
  // Standard crc7 polynomial x^7 + x^3 + 1
  // Standard crc16 polynomial x^16 + x^12 + x^5 + 1
  // Standard crc32 polynomial x^32 + x^26 + x^23 + x^22 + x^16 + x^12 +
  //                                 x^11 + x^10 + x^8 + x^7 + x^5 + x^4 + x^2 +
  //                                 x^1 + 1
  // Standard CRC64 polynomial x^64 + x^4 + x^3 + x^1 + 1 

  assign crc_function_poly_in = (crc_poly_specified === 1) ? polynomial : 
                                 ((standard_polynomial === 1) ? crc5    :
                                  (standard_polynomial === 2) ? crc7    :
                                  (standard_polynomial === 3) ? crc16   :
                                  (standard_polynomial === 4) ? crc32   :
                          (standard_polynomial === 5) ? 64'h0000_0000_0000_001b: {temp_crc_width{1'b0}});

  assign initial_crc_value = (int_initial_crc_value === 0) ? {temp_crc_width{1'b0}} :
                             (int_initial_crc_value === 1) ? {temp_crc_width{1'b0}} :
                             (int_initial_crc_value === 2) ? {temp_crc_width{1'b1}} :
                             (int_initial_crc_value === 3) ? {((temp_crc_width+1)/2){2'b01}} :
                             (int_initial_crc_value === 4) ? {((temp_crc_width+1)/2){2'b10}} : {temp_crc_width{1'b0}};

  // At the start of CRC computation initil CRC register value will be driven
  // into this variable, afterwards the computed CRC value will be driven.
  
  assign new_crc_value = (start_crc || latch_crc) ? initial_crc_value : r_combo_crc;

  // If crc is not specified and temp_crc_width is greater than the Width of
  // data bus, then we have to compare the CRC value across so many clocks.
  // Following two variables will give the sliced CRC values across that
  // many number of clocks.

  assign temp_expected_crc = (in_crc_specified === 1'b0 &&
                             temp_crc_width >= width) ?
                             ((compare_crc_enable && r_compare_crc_enable ===
                              1'b0 && !latch_crc_specified) ? 
                  ((big_endian && !reverse_endian) ||
                      (!big_endian && reverse_endian)) ?
                              final_crc[temp_crc_width-1:
                              temp_crc_width-temp_crc_a] :
                              final_crc[temp_crc_a-1:0] : 
                  ((big_endian && !reverse_endian) ||
                              (!big_endian && reverse_endian)) ? 
                              temp_expected_crc_value[temp_crc_width-1 :
                              temp_crc_width-temp_crc_a] :
                              temp_expected_crc_value[temp_crc_a-1:0]) :
                              final_crc;

  assign temp_latched_crc = (in_crc_specified === 1'b0 &&
                             temp_crc_width >= width) ?
                             ((compare_crc_enable && r_compare_crc_enable ===
                             1'b0 && latch_crc_specified) ? 
                             ((big_endian && !reverse_endian) ||
                             (!big_endian && reverse_endian)) ?
                             latch_crc_reg[temp_crc_width-1:
                             temp_crc_width-temp_crc_a] :
                             latch_crc_reg[temp_crc_a - 1:0] :
                             ((big_endian && !reverse_endian) ||
                             (!big_endian && reverse_endian)) ?
                             temp_latch_crc_value[temp_crc_width-1:
                             temp_crc_width-temp_crc_a] :
                             temp_latch_crc_value[temp_crc_a-1:0]) :
                             final_crc;

  assign latched_crc_value = (in_crc_specified === 1'b0) ? temp_latched_crc :
                              latch_crc_reg;

  assign calculated_crc_value = (in_crc_specified === 1'b0) ? temp_expected_crc :
                 final_crc;

  assign computed_crc_value = (latch_crc_specified === 1) ?
                               latched_crc_value : calculated_crc_value;

  // The final computed CRC value, which is used for CRC comparison. 
  // If invert option is specified the computed CRC value will be 
  // inverted before comparison else it will be directly taken for comparison.

  assign final_crc_value = invert ? ~computed_crc_value :
                           computed_crc_value;

  // Not specifying crc indicates availability of CRC on the data bus. The
  // checker will not compute CRC during the CRC phase (when -compare_crc enable
  // is asserted) on the bus, but will compare the CRC. 

  assign not_compute_crc = (in_crc_specified === 0 && compare_crc_enable);

  // If data bus width and crc_computation_width_internal both are not same, then the
  // incoming data bits will be accumulated in this variable and then CRC will 
  // be computed for the accumulated data.

  assign accumulation_reg = crc_comp_count ? test_expr :
                            (not_compute_crc === 1'b0 && !xz_detected_in_valid
                            && in_data_valid) ?
                            (big_endian ? {temp_accumulation_reg[acc_reg_width:0],
                             test_expr} : {test_expr,
                             temp_accumulation_reg[crc_computation_width_internal-1:
                             crc_computation_width_internal-acc_reg_width-1]}):
                             temp_accumulation_reg;

  assign in_crc_value = (in_crc_specified) ? crc : test_expr;

  // This assignment statement will determine which data has to be passed 
  // to the CRC function. (Either swapped accumulated data or accumulated
  // data.

  assign final_data = (lsb_first === 1) ? swap_data : accumulation_reg;

//------------------------------------------------------------------------
// Calling the CRC function depending upon the polynomial specified.
//------------------------------------------------------------------------
  assign combo_crc = in_data_valid === 1'b1
                        ? (((start_crc || latch_crc) && 
                            crc_comp_count === 0) ? initial_crc_value 
                                                : ((compute_crc === 1'b1 && 
                                                    compute_crc_flag === 1'b1 &&
                                                    not_compute_crc === 1'b0
                                                   )?expected_crc(new_crc_value,
                                                                  final_data,
                                                          crc_function_poly_in)
                                                    : r_combo_crc 
                                                  )
                          )
                        : ((start_crc || latch_crc) ? initial_crc_value 
                                                        : r_combo_crc 
                          );

  assign final_crc = combinational ? combo_crc : r_combo_crc;

  // Assertion Logic for combinatorial fire signal

  assign crc_fire_combo = (compare_crc_enable && (final_crc_value !== in_crc_value));

  assign crc_check_fire_combo = (reset === 1'b1 && enable === 1'b1 && crc_fire_combo === 1'b1);
               
`ifdef OVL_SYNTHESIS
`else
  initial begin
    total_crc_computations  = {stat_cnt_width{1'b0}};
    cycles_checked          = {stat_cnt_width{1'b0}};
    r_combo_crc             = {temp_crc_width{1'b0}}; 
    latch_crc_reg           = {temp_crc_width{1'b0}};
    temp_expected_crc_value = {temp_crc_width{1'b0}};
    temp_latch_crc_value    = {temp_crc_width{1'b0}};
    r_compare_crc_enable    = 1'b0;
    r_compute_crc_flag      = 1'b0;
    crc_comp_width_counter  = {(crc_comp_counter_width+1){1'b0}};
    temp_accumulation_reg   = {crc_computation_width_internal{1'b0}};
    swap_data               = {crc_computation_width_internal{1'b0}};
  end
`endif
  
  // Logic for swapping the data content
  always @ (accumulation_reg or compute_crc_flag)
    begin
      acc_reg = accumulation_reg;
      swap_data = {crc_computation_width_internal{1'b0}}; 
      temp_compute_crc_flag = compute_crc_flag; 
      if (lsb_first === 1 && temp_compute_crc_flag === 1'b1)
    begin
      for (bit_loop_count=0;bit_loop_count < crc_computation_width_internal;bit_loop_count=bit_loop_count+1)
         begin
           swap_data[(crc_computation_width_internal-1)-bit_loop_count] = acc_reg[bit_loop_count];
             end
    end 
      else 
    swap_data = swap_data;
    end

  // Sequential block
  always @( posedge clock )
    begin
      if(`OVL_RESET_SIGNAL != 1'b1)
        begin
          r_combo_crc             <= {temp_crc_width{1'b0}}; 
          latch_crc_reg           <= {temp_crc_width{1'b0}};
          crc_comp_width_counter  <= {(crc_comp_counter_width+1){1'b0}};
          temp_expected_crc_value <= {temp_crc_width{1'b0}};
          temp_latch_crc_value    <= {temp_crc_width{1'b0}};
          r_compare_crc_enable    <= 1'b0;
          r_compute_crc_flag      <= 1'b0;
          temp_accumulation_reg   <= {crc_computation_width_internal{1'b0}};
      total_crc_computations  <= {stat_cnt_width{1'b0}};
      cycles_checked          <= {stat_cnt_width{1'b0}};
        end
      else if (enable === 1'b1)
        begin
           r_combo_crc <= combo_crc; 

          if (in_data_valid === 1'b1)
            begin

              r_compare_crc_enable <= compare_crc_enable;
              r_compute_crc_flag <= compute_crc_flag;

              //----------------------------------------------------------
              // crc is not specified and width is less than the 
              // width of CRC register.
              //----------------------------------------------------------

              if (in_crc_specified === 1'b0)
                begin
                  if (!latch_crc_specified)
                    begin
                      if (compare_crc_enable && r_compare_crc_enable === 1'b0)
                        begin
                          if ((big_endian && reverse_endian) ||
                  (!big_endian && !reverse_endian)) 
                            temp_expected_crc_value <= (final_crc >> width);
                          else
                            temp_expected_crc_value <= (final_crc << width);
                        end     
                      else
                        begin
                          if ((big_endian && reverse_endian) ||
                              (!big_endian && !reverse_endian)) 
                            temp_expected_crc_value <= (temp_expected_crc_value >> width);
                          else
                            temp_expected_crc_value <= (temp_expected_crc_value << width);
                        end
                    end
                  else
                    begin
                      if (compare_crc_enable && r_compare_crc_enable === 1'b0)
                        begin
                          if ((big_endian && reverse_endian) ||
                              (!big_endian && !reverse_endian)) 
                            temp_latch_crc_value <= (latch_crc_reg >> width);
                          else
                            temp_latch_crc_value <= (latch_crc_reg << width);
                        end
                      else
                        begin
                          if ((big_endian && reverse_endian) ||
                              (!big_endian && !reverse_endian)) 
                            temp_latch_crc_value <= (temp_latch_crc_value >> width);
                          else
                            temp_latch_crc_value <= (temp_latch_crc_value << width);
                        end
                    end
                end

                   temp_accumulation_reg <= accumulation_reg;

                  //----------------------------------------------------------
                  // Counter logic for accumulating the data bits
                  //----------------------------------------------------------
                  
                  if (crc_comp_width_counter !== width && 
                      !start_crc &&
                      !latch_crc && not_compute_crc === 1'b0 &&
                      xz_detected_in_valid === 1'b0 &&
              r_compute_crc_flag === 1'b0)
                    begin
                      crc_comp_width_counter <= (crc_comp_width_counter - width);
                    end
                  else 
                    begin
                      crc_comp_width_counter <= (crc_computation_width_internal-width); 
                    end

                  //--------------------------------------------------
                  // If latch_crc signal is sampled asserted computed
                  // CRC value will be stored in the latch_crc_reg 
                  //--------------------------------------------------
 
                  if (latch_crc)
                    latch_crc_reg <= final_crc;

`ifdef OVL_COVER_ON
                  //---------------------------------------------------
                  // Updation of Total CRC computation statistics
                  //---------------------------------------------------

                  if (compute_crc === 1'b1 && compute_crc_flag === 1'b1 &&
                      not_compute_crc === 1'b0 && 
              total_crc_computations != {stat_cnt_width{1'b1}})
                    total_crc_computations <= total_crc_computations + 1'b1;
`endif
            end
         else if (start_crc || latch_crc)
       begin
         crc_comp_width_counter <= crc_computation_width_internal;
             if(latch_crc)
               latch_crc_reg <= final_crc; // Latch the CRC
       end 

             //------------------------------------------------
             // Updation of cornercase statistics
             //------------------------------------------------ 

`ifdef OVL_COVER_ON
             if (compare_crc_enable && (not_compute_crc === 1'b1 ||
                 in_crc_specified) && cycles_checked != {stat_cnt_width{1'b1}})
               cycles_checked <= cycles_checked + 1'b1;
`endif
        end
    end

`endif // OVL_SHARED_CODE


`ifdef OVL_ASSERT_ON

  property OVL_CRC_CHECK_P;
  @(posedge clock)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
      (crc_check_fire_combo == 1'b0);
  endproperty

 `ifdef OVL_XCHECK_OFF
    // Do nothing
 `else

  `ifdef OVL_IMPLICIT_XCHECK_OFF
    // Do Nothing
  `else

  property OVL_CRC_XZ_IN_TEST_EXPR_P;
  @(posedge clock)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
      (!($isunknown(test_expr)));
  endproperty

  property OVL_CRC_XZ_IN_START_CRC_P;
  @(posedge clock)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
      (!($isunknown(initialize)));
  endproperty

  property OVL_CRC_XZ_IN_VALID_P;
  @(posedge clock)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
      (!($isunknown(valid)));
  endproperty

  property OVL_CRC_XZ_IN_LATCH_CRC_P;
  @(posedge clock)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
      (!($isunknown(crc_latch)));
  endproperty

  property OVL_CRC_XZ_IN_CRC_P;
  @(posedge clock)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
      (!($isunknown(crc)));
  endproperty

  property OVL_CRC_XZ_IN_COMPARE_P;
  @(posedge clock)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
      (!($isunknown(compare)));
  endproperty

  `endif // OVL_IMPLICIT_XCHECK_OFF
 `endif // OVL_XCHECK_OFF

  generate
    case (property_type)
      `OVL_ASSERT_2STATE,
      `OVL_ASSERT: begin : ovl_assert

           A_OVL_CRC_CHECK_P:
           assert property (OVL_CRC_CHECK_P)
           else begin
             ovl_error_t(`OVL_FIRE_2STATE,"Input CRC value did not match the expected CRC value");
             error_event = 1;
       end  

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
         
     A_OVL_CRC_XZ_IN_TEST_EXPR_P:
         assert property (OVL_CRC_XZ_IN_TEST_EXPR_P)
         else begin
           ovl_error_t(`OVL_FIRE_XCHECK,"test_expr contains X or Z");
           error_event_xz = 1;
         end

         A_OVL_CRC_XZ_IN_START_CRC_P:
         assert property (OVL_CRC_XZ_IN_START_CRC_P)
         else begin
           ovl_error_t(`OVL_FIRE_XCHECK,"initialize contains X or Z");
           error_event_xz = 1;
         end

         A_OVL_CRC_XZ_IN_VALID_P:
         assert property (OVL_CRC_XZ_IN_VALID_P)
         else begin
           ovl_error_t(`OVL_FIRE_XCHECK,"valid contains X or Z");
           error_event_xz = 1;
           xz_detected_in_valid = 1;
         end

         A_OVL_CRC_XZ_IN_LATCH_CRC_P:
         assert property (OVL_CRC_XZ_IN_LATCH_CRC_P)
         else begin
           ovl_error_t(`OVL_FIRE_XCHECK,"crc_latch contains X or Z");
           error_event_xz = 1;
         end

         A_OVL_CRC_XZ_IN_CRC_P:
         assert property (OVL_CRC_XZ_IN_CRC_P)
         else begin
           ovl_error_t(`OVL_FIRE_XCHECK,"crc contains X or Z");
           error_event_xz = 1;
         end

         A_OVL_CRC_XZ_IN_COMPARE_P:
         assert property (OVL_CRC_XZ_IN_COMPARE_P)
         else begin
           ovl_error_t(`OVL_FIRE_XCHECK," contains X or Z");
           error_event_xz = 1;
         end

  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

      end

      `OVL_ASSUME_2STATE,
      `OVL_ASSUME: begin : ovl_assume
      
         M_OVL_CRC_CHECK_P:
         assume property (OVL_CRC_CHECK_P);

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else

    M_OVL_CRC_XZ_IN_TEST_EXPR_P:
        assume property (OVL_CRC_XZ_IN_TEST_EXPR_P);

        M_OVL_CRC_XZ_IN_START_CRC_P:
        assume property (OVL_CRC_XZ_IN_START_CRC_P);

        M_OVL_CRC_XZ_IN_VALID_P:
        assume property (OVL_CRC_XZ_IN_VALID_P);
        
    M_OVL_CRC_XZ_IN_LATCH_CRC_P:
        assume property (OVL_CRC_XZ_IN_LATCH_CRC_P);

        M_OVL_CRC_XZ_IN_CRC_P:
        assume property (OVL_CRC_XZ_IN_CRC_P);

        M_OVL_CRC_XZ_IN_COMPARE_P:
        assume property (OVL_CRC_XZ_IN_COMPARE_P);

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

      if (OVL_COVER_BASIC_ON) begin : ovl_cover_basic

        cover_crc_value_check :
          cover property (
            @(posedge clock)
             (`OVL_RESET_SIGNAL != 1'b0) && !$stable(crc))
             ovl_cover_t("CRC changed value");

      end : ovl_cover_basic

      if (OVL_COVER_STATISTIC_ON) begin : ovl_cover_statistic
        
    cover_crc_computations_checked :
          cover property (
            @(posedge clock)
             (`OVL_RESET_SIGNAL != 1'b0) && !$stable(total_crc_computations))
             ovl_cover_t("Total CRC Computations changed value");

      end : ovl_cover_statistic

      if (OVL_COVER_CORNER_ON) begin : ovl_cover_corner

        cover_cycles_checked:
            cover property (
            @(posedge clock)
             (`OVL_RESET_SIGNAL != 1'b0) && !$stable(cycles_checked))
             ovl_cover_t("Cycles Checked changed value");

      end : ovl_cover_corner

    end : ovl_cover

  endgenerate

`endif // OVL_COVER_ON

