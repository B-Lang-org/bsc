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
    assign  fire[0] = error_event;
    assign  fire[1] = error_event_xz;
  `else
    assign  fire[0] = 1'b0;
    assign  fire[1] = 1'b0;
  `endif // OVL_ASSERT_ON

  `ifdef OVL_COVER_ON
    assign fire[2] = 1'b0;
  `else
    assign fire[2] = 1'b0;
  `endif // OVL_COVER_ON
`endif // OVL_REVISIT

`ifdef OVL_SYNTHESIS
`else
  initial
    begin
      if(min_hold <= 0)
    ovl_error_t(`OVL_FIRE_2STATE,"Illegal value for min_hold parameter which must be greater than 0");
      if(max_hold<min_hold && max_hold != 0)
    ovl_error_t(`OVL_FIRE_2STATE,"Illegal value for max_hold parameter which must be either 0 or greater than min_hold");
    end
`endif

`ifdef OVL_SHARED_CODE
  // Global declaration
  reg                        sva_checker_time_0;
  wire                       sva_states_combo;
  reg [next_count*width-1:0] next_state_reg;
  reg                        sva_states;

  assign                     sva_states_combo = (disallow==1)? ~sva_states:sva_states;

                        
  // Initialization of global variable

`ifdef OVL_SYNTHESIS
`else
  initial
    begin
      sva_checker_time_0=1'b1;
      sva_states=0;
    end // initial begin
`endif
  // Logic for checking whether test_expr is equal to one of the next state or not
  always @(test_expr or sva_checker_time_0)
    begin
      next_state_reg=next_state;
      sva_states=1'b0;
      repeat(next_count)
    begin : loop
      if(test_expr== next_state_reg[width-1:0])
        sva_states=1'b1;
      next_state_reg = next_state_reg >> width;
    end
    end

  // logic for updating covergae variables
  always @(posedge clk )
    begin
      if(`OVL_RESET_SIGNAL != 1'b1)
    begin
          sva_checker_time_0<=1'b1;
    end
      else
    begin
      sva_checker_time_0 <= 1'b0;
        end // else: !if(`OVL_RESET_SIGNAL != 1'b1)
    end // always @ (posedge clk )

  // function checks whether test_expr exists in nex_state or not
   /* function sva_states;
     input dummy;
     reg  [next_count*width-1:0]  next_state_reg;
     next_state_reg=next_state;
     sva_states=1'b0;
     repeat(next_count)
       begin : loop
    if(test_expr== next_state_reg[width-1:0])
      sva_states=1'b1;
     next_state_reg = next_state_reg >> width;
       end
     if(disallow==1)
       sva_states=~sva_states;
    endfunction*/

  sequence sva_s_next_states_1;
    ($stable( test_expr))[*min_hold-1 : $] ##1 sva_states_combo;
  endsequence

  sequence sva_s_next_states_2;
    (test_expr == curr_state)[*min_hold-1 : max_hold-1] ##1 sva_states_combo;
  endsequence

  sequence sva_s_next_states_3;
    ($stable( test_expr))[*min_hold-1 : $] ##1 ( test_expr != curr_state) ##0 sva_states_combo;
  endsequence

  sequence sva_s_next_states_4;
    (test_expr == curr_state)[*min_hold-1 : max_hold-1] ##1 ( test_expr != curr_state) ##0 sva_states_combo;
  endsequence

  property OVL_NEXT_STATE_CHECK_P_1;
    @(posedge  clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
      (!$stable(test_expr) || sva_checker_time_0) && ( test_expr == curr_state) |=> sva_s_next_states_1;
  endproperty

  property OVL_NEXT_STATE_CHECK_P_2;
    @(posedge  clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
      (!$stable(test_expr) || sva_checker_time_0) && ( test_expr == curr_state) |=> sva_s_next_states_2;
  endproperty

  property OVL_NEXT_STATE_CHECK_P_3;
    @(posedge  clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
      (!$stable(test_expr) || sva_checker_time_0) && ( test_expr == curr_state) |=> sva_s_next_states_3;
  endproperty

  property OVL_NEXT_STATE_CHECK_P_4;
    @(posedge  clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
      (!$stable(test_expr) || sva_checker_time_0) && ( test_expr == curr_state) |=> sva_s_next_states_4;
  endproperty

`endif

`ifdef OVL_ASSERT_ON

 `ifdef OVL_XCHECK_OFF
    // Do nothing
 `else

  `ifdef OVL_IMPLICIT_XCHECK_OFF
    // Do Nothing
  `else
    property OVL_NEXT_STATE_XZ_ON_TEST_EXPR_P;
  @(posedge  clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
      (!($isunknown(test_expr)));
  endproperty

    property OVL_NEXT_STATE_XZ_ON_CURR_STATE_P;
  @(posedge  clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
      (!($isunknown(curr_state)));
  endproperty

    property OVL_NEXT_STATE_XZ_ON_NEXT_STATE_P;
     @(posedge  clk)
       disable iff (`OVL_RESET_SIGNAL != 1'b1)
     (!($isunknown(next_state)));
  endproperty
       `endif // OVL_IMPLICIT_XCHECK_OFF
       `endif // OVL_XCHECK_OFF
       // Checker assertion code begin here
    generate
      // Assert property starts here
      // Assertions
      case(property_type)
    `OVL_ASSERT:
      begin : ovl_assert
        if(( max_hold ==0) && disallow==0)
          begin : assert_check_p_1
        A_OVL_NEXT_STATE_CHECK_P:
          assert property (OVL_NEXT_STATE_CHECK_P_1)
            else
            begin
              ovl_error_t(`OVL_FIRE_2STATE,"Match occurred but expression value was not a next value, or expression changed too soon");
              error_event = 1;
            end
          end
        if( ( min_hold > 0) &&  ( max_hold >= min_hold) && disallow==0)
          begin : assert_check_p_2
        A_OVL_NEXT_STATE_CHECK_P:
          assert property (OVL_NEXT_STATE_CHECK_P_2)
            else
            begin
              ovl_error_t(`OVL_FIRE_2STATE,"Match occurred but expression value was not a next value, or expression did not change in event window");
              error_event = 1;
            end
          end
        if(( max_hold ==0) && disallow==1)
          begin : assert_check_p_3
        A_OVL_NEXT_STATE_CHECK_P:
          assert property (OVL_NEXT_STATE_CHECK_P_3)
            else
            begin
              ovl_error_t(`OVL_FIRE_2STATE,"Match occurred but expression value was a next value, or expression changed too soon");
              error_event = 1;
            end
          end
        if( ( min_hold > 0) &&  ( max_hold >= min_hold) && disallow==1)
          begin : assert_check_p_4
        A_OVL_NEXT_STATE_CHECK_P:
          assert property (OVL_NEXT_STATE_CHECK_P_4)
            else
            begin
              ovl_error_t(`OVL_FIRE_2STATE,"Match occurred but expression value was a next value, or expression did not change in event window");
              error_event = 1;
            end
          end
    
       `ifdef OVL_XCHECK_OFF
        //Do nothing
       `else
    `ifdef OVL_IMPLICIT_XCHECK_OFF
        //Do nothing
    `else
    
        A_OVL_NEXT_STATE_XZ_ON_TEST_EXPR_P:
          assert property (OVL_NEXT_STATE_XZ_ON_TEST_EXPR_P)
            else
            begin
              ovl_error_t(`OVL_FIRE_XCHECK,"test_expr contains X or Z");
              error_event_xz = 1;
            end
    
        A_OVL_NEXT_STATE_XZ_ON_CURR_STATE_P:
          assert property (OVL_NEXT_STATE_XZ_ON_CURR_STATE_P)
            else
            begin
              ovl_error_t(`OVL_FIRE_XCHECK,"curr_state contains X or Z");
              error_event_xz = 1;
            end

        A_OVL_NEXT_STATE_XZ_ON_NEXT_STATE_P:
          assert property (OVL_NEXT_STATE_XZ_ON_NEXT_STATE_P)
            else
            begin
              ovl_error_t(`OVL_FIRE_XCHECK,"next_state contains X or Z");
              error_event_xz = 1;
            end
    `endif // OVL_IMPLICIT_XCHECK_OFF
       `endif // OVL_XCHECK_OFF
      end // block: ovl_assert
    

    `OVL_ASSUME:
      begin :ovl_assume
        if(( max_hold ==0) && disallow==0)
          M_OVL_NEXT_STATE_CHECK_P:
        assume property (OVL_NEXT_STATE_CHECK_P_1);
        if( ( min_hold > 0) &&  ( max_hold >= min_hold) && disallow==0)
          M_OVL_NEXT_STATE_CHECK_P:
        assume property (OVL_NEXT_STATE_CHECK_P_2);
        if(( max_hold ==0) && disallow==1)
          M_OVL_NEXT_STATE_CHECK_P:
        assume property (OVL_NEXT_STATE_CHECK_P_3);
        if( ( min_hold > 0) &&  ( max_hold >= min_hold) && disallow==1)
          M_OVL_NEXT_STATE_CHECK_P:
        assume property (OVL_NEXT_STATE_CHECK_P_4);
    
       `ifdef OVL_XCHECK_OFF
        //Do nothing
       `else
    `ifdef OVL_IMPLICIT_XCHECK_OFF
        //Do nothing
    `else
        M_OVL_NEXT_STATE_XZ_ON_TEST_EXPR_P:
          assume property (OVL_NEXT_STATE_XZ_ON_TEST_EXPR_P);
        M_OVL_NEXT_STATE_XZ_ON_CURR_STATE_P:
          assume property (OVL_NEXT_STATE_XZ_ON_CURR_STATE_P);
        M_OVL_NEXT_STATE_XZ_ON_NEXT_STATE_P:
          assume property (OVL_NEXT_STATE_XZ_ON_NEXT_STATE_P);
    `endif // OVL_IMPLICIT_XCHECK_OFF
       `endif // OVL_XCHECK_OFF
    
      end // block: ovl_assume
    `OVL_IGNORE:
      begin :ovl_ignore
       // Do Nothing;
      end
    default :
      begin
        initial
          ovl_error_t(`OVL_FIRE_2STATE,"");
           end
      endcase
    endgenerate
      `endif // OVL_ASSERT_ON


`ifdef OVL_COVER_ON

`ifdef OVL_COVERGROUP_ON

  // coverage variable
  integer                    cycles_checked;
  integer                    number_of_transitions_covered;
  wire                       all_transitions_covered;
  reg [next_count*width-1:0] next_tmp;
  reg                        event_window_started;
  integer                    trans_count;
  reg [next_count-1:0]       transitions_used;
  integer                    i;

  assign              all_transitions_covered = &transitions_used;


 // Initialization of cover variable

`ifdef OVL_SYNTHESIS
`else
  initial
    begin
      cycles_checked=0;
      number_of_transitions_covered=0;
      transitions_used=0;
    end // initial begin
`endif

  always @(posedge clk )
    begin
      if(`OVL_RESET_SIGNAL == 1'b1)
    begin
      cycles_checked <= ((!$stable(test_expr) || sva_checker_time_0) && ( test_expr == curr_state))?cycles_checked+1:cycles_checked;
      event_window_started <= ((!$stable(test_expr) || sva_checker_time_0) && ( test_expr == curr_state))?1'b1:1'b0;
          next_tmp = next_state;
      for (i=0; i<next_count; i=i+1)
        begin
          if (event_window_started && test_expr==next_tmp[width-1:0])
        begin
          transitions_used[i] = 1'b1;
          event_window_started=1'b0;
        end
          next_tmp = next_tmp >> width;
        end
      trans_count=0;
      for (i=0; i<next_count; i=i+1)
        begin
          if (transitions_used[i] == 1'b1)
                trans_count = trans_count + 1;
        end // for (i=0; i<NEXT_ITEM_COUNT; i=i+1)
      number_of_transitions_covered <= trans_count;
    end
    end // always @ (posedge clk )



  // Covergroup starts here
  covergroup OVL_NEXT_STATE_CORNER @ (posedge clk);
  cover_all_transitions : coverpoint (!($stable(all_transitions_covered,  @ (posedge clk))))
    iff (`OVL_RESET_SIGNAL != 1'b0)
      {
       bins All_Transitions_Covered = {1};
       option.comment = "All Transitions Covered";
       }
  endgroup
            
  covergroup OVL_NEXT_STATE_STATISTIC @ (posedge clk);
  observed_transitions : coverpoint (!($stable(number_of_transitions_covered, @ (posedge clk))))
       iff (`OVL_RESET_SIGNAL != 1'b0 )
     {
      bins Number_of_Transitions_Covered = {1};
      option.at_least = 1;
      option.comment = "Number of Transitions Covered";
      }
       cover_cycles_checked : coverpoint (!($stable(cycles_checked, @ (posedge clk))))
     iff (`OVL_RESET_SIGNAL != 1'b0 )
       {
            bins Cycles_Checked = {1};
    option.at_least = 1;
            option.comment = "Cycles Checked";
            }            
   endgroup         

`endif  // `ifdef OVL_COVERGROUP_ON
            
 generate
   genvar g1,g2,g3;
   if (coverage_level != `OVL_COVER_NONE)
     begin : ovl_cover
       if(OVL_COVER_SANITY_ON)
     begin :ovl_cover_sanity
       if( max_hold == 0 && disallow==0)
         begin : cover_check_p_1
           cover_transitions_to_next_state:
         cover property (OVL_NEXT_STATE_CHECK_P_1)
           ovl_cover_t("next state transition covered");
         end // if ( ( min_hold > 0) && ( ( max_hold >= min_hold) || max_hold == 0))
       if( min_hold > 0 && max_hold >= min_hold && disallow ==0)
         begin : cover_check_p_2
           cover_transitions_to_next_state:
         cover property (OVL_NEXT_STATE_CHECK_P_2)
           ovl_cover_t("next state transition covered");
         end // if ( ( min_hold > 0) && ( ( max_hold >= min_hold) || max_hold == 0))
       if( max_hold == 0 && disallow==1)
         begin :cover_check_p_3
           cover_transitions_to_next_state:
         cover property (OVL_NEXT_STATE_CHECK_P_3)
           ovl_cover_t("next state transition covered");
         end // if ( ( min_hold > 0) && ( ( max_hold >= min_hold) || max_hold == 0))
       if( min_hold > 0 && max_hold >= min_hold && disallow==1)
         begin :cover_check_p_4
           cover_transitions_to_next_state:
         cover property (OVL_NEXT_STATE_CHECK_P_4)
           ovl_cover_t("next state transition covered");
         end
     end : ovl_cover_sanity
    
       if(OVL_COVER_BASIC_ON)
         begin:ovl_cover_basic
    
         end

       if(OVL_COVER_CORNER_ON)
     begin:ovl_cover_corner
`ifdef OVL_COVERGROUP_ON
       if(disallow==0)
         OVL_NEXT_STATE_CORNER NEXT_STATE_CORNER = new();
`endif
     end // block: ovl_cover_corner

       if(OVL_COVER_STATISTIC_ON)
     begin:ovl_cover_statistic
`ifdef OVL_COVERGROUP_ON
       if(disallow==0)
         OVL_NEXT_STATE_STATISTIC NEXT_STATE_STATISTIC = new();
`endif
     end
     end // ovl_cover
 endgenerate

       `endif




