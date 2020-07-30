// Accellera Standard V2.8.1 Open Verification Library (OVL).
// Accellera Copyright (c) 2005-2014. All rights reserved.




`ifdef OVL_ASSERT_ON

`ifdef OVL_END_OF_SIMULATION
    property ASSERT_QUIESCENT_STATE_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    ##1($rose(`OVL_END_OF_SIMULATION) ||
     $rose(sample_event)) |-> (state_expr == check_value);
    endproperty

  `ifdef OVL_XCHECK_OFF
    //Do nothing
  `else
    `ifdef OVL_IMPLICIT_XCHECK_OFF
      //Do nothing
    `else
      property ASSERT_QUIESCENT_STATE_XZ_ON_EOS_P;
      @(posedge clk)
      disable iff (`OVL_RESET_SIGNAL != 1'b1)
      ((!($isunknown(($past(`OVL_END_OF_SIMULATION)))) && !(($past(`OVL_END_OF_SIMULATION)))
        && !($isunknown(`OVL_END_OF_SIMULATION))) ||
       (!($isunknown(($past(`OVL_END_OF_SIMULATION)))) && (($past(`OVL_END_OF_SIMULATION)))) ||
       (($isunknown(($past(`OVL_END_OF_SIMULATION)))) && !($isunknown(`OVL_END_OF_SIMULATION))
         && !(`OVL_END_OF_SIMULATION) ));
      endproperty

      property ASSERT_QUIESCENT_STATE_XZ_ON_STATE_EXPR_P;
      @(posedge clk)
      disable iff (`OVL_RESET_SIGNAL != 1'b1)
      ($rose(`OVL_END_OF_SIMULATION) ||
             $rose(sample_event)) |-> (!($isunknown(state_expr)));
      endproperty

      property ASSERT_QUIESCENT_STATE_XZ_ON_CHECK_VALUE_P;
      @(posedge clk)
      disable iff (`OVL_RESET_SIGNAL != 1'b1)
      ($rose(`OVL_END_OF_SIMULATION) ||
       $rose(sample_event)) |-> (!($isunknown(check_value)));
      endproperty
    `endif // OVL_IMPLICIT_XCHECK_OFF
  `endif // OVL_XCHECK_OFF
`else
    property ASSERT_QUIESCENT_STATE_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    $rose(sample_event) |-> (state_expr == check_value);
    endproperty

  `ifdef OVL_XCHECK_OFF
    //Do nothing
  `else
    `ifdef OVL_IMPLICIT_XCHECK_OFF
      //Do nothing
    `else
      property ASSERT_QUIESCENT_STATE_XZ_ON_STATE_EXPR_P;
      @(posedge clk)
      disable iff (`OVL_RESET_SIGNAL != 1'b1)
      $rose(sample_event) |-> (!($isunknown(state_expr)));
      endproperty

      property ASSERT_QUIESCENT_STATE_XZ_ON_CHECK_VALUE_P;
      @(posedge clk)
      disable iff (`OVL_RESET_SIGNAL != 1'b1)
      $rose(sample_event) |-> (!($isunknown(check_value)));
      endproperty
   `endif // OVL_IMPLICIT_XCHECK_OFF
 `endif // OVL_XCHECK_OFF
`endif // OVL_END_OF_SIMULATION

`ifdef OVL_XCHECK_OFF
    //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
    property ASSERT_QUIESCENT_STATE_XZ_ON_SAMPLE_EVENT_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    ((!($isunknown(($past(sample_event)))) && !(($past(sample_event)))
      && !($isunknown(sample_event))) ||
     (!($isunknown(($past(sample_event)))) && (($past(sample_event)))) ||
     (($isunknown(($past(sample_event)))) && !($isunknown(sample_event))
       && !(sample_event) ));
    endproperty
  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

  generate

    case (property_type)
      `OVL_ASSERT_2STATE,
      `OVL_ASSERT: begin : ovl_assert
        A_ASSERT_QUIESCENT_STATE_P: assert property (ASSERT_QUIESCENT_STATE_P)
                                    else ovl_error_t(`OVL_FIRE_2STATE,"State expression is not equal to check_value while sample event is asserted");

    `ifdef OVL_XCHECK_OFF
        //Do nothing
    `else
      `ifdef OVL_IMPLICIT_XCHECK_OFF
        //Do nothing
      `else
        A_ASSERT_QUIESCENT_STATE_XZ_ON_STATE_EXPR_P:
        assert property (ASSERT_QUIESCENT_STATE_XZ_ON_STATE_EXPR_P)
        else ovl_error_t(`OVL_FIRE_XCHECK,"state_expr contains X or Z");

        A_ASSERT_QUIESCENT_STATE_XZ_ON_CHECK_VALUE_P:
        assert property (ASSERT_QUIESCENT_STATE_XZ_ON_CHECK_VALUE_P)
        else ovl_error_t(`OVL_FIRE_XCHECK,"check_value contains X or Z");

        A_ASSERT_QUIESCENT_STATE_XZ_ON_SAMPLE_EVENT_P:
        assert property (ASSERT_QUIESCENT_STATE_XZ_ON_SAMPLE_EVENT_P)
        else ovl_error_t(`OVL_FIRE_XCHECK,"sample_event contains X or Z");

        `ifdef OVL_END_OF_SIMULATION
          A_ASSERT_QUIESCENT_STATE_XZ_ON_EOS_P:
          assert property (ASSERT_QUIESCENT_STATE_XZ_ON_EOS_P)
          else ovl_error_t(`OVL_FIRE_XCHECK,"`OVL_END_OF_SIMULATION contains X or Z");
        `endif // OVL_END_OF_SIMULATION

      `endif // OVL_IMPLICIT_XCHECK_OFF
    `endif // OVL_XCHECK_OFF

      end
      `OVL_ASSUME_2STATE,
      `OVL_ASSUME: begin : ovl_assume
        M_ASSERT_QUIESCENT_STATE_P: assume property (ASSERT_QUIESCENT_STATE_P);

    `ifdef OVL_XCHECK_OFF
        //Do nothing
    `else
      `ifdef OVL_IMPLICIT_XCHECK_OFF
        //Do nothing
      `else
        M_ASSERT_QUIESCENT_STATE_XZ_ON_STATE_EXPR_P:
        assume property (ASSERT_QUIESCENT_STATE_XZ_ON_STATE_EXPR_P);

        M_ASSERT_QUIESCENT_STATE_XZ_ON_CHECK_VALUE_P:
        assume property (ASSERT_QUIESCENT_STATE_XZ_ON_CHECK_VALUE_P);

        M_ASSERT_QUIESCENT_STATE_XZ_ON_SAMPLE_EVENT_P:
        assume property (ASSERT_QUIESCENT_STATE_XZ_ON_SAMPLE_EVENT_P);

        `ifdef OVL_END_OF_SIMULATION
          M_ASSERT_QUIESCENT_STATE_XZ_ON_EOS_P:
          assume property (ASSERT_QUIESCENT_STATE_XZ_ON_EOS_P);
        `endif // OVL_END_OF_SIMULATION

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

