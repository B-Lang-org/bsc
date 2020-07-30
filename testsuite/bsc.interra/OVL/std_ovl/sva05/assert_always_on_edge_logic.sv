// Accellera Standard V2.8.1 Open Verification Library (OVL).
// Accellera Copyright (c) 2005-2014. All rights reserved.



`ifdef OVL_ASSERT_ON

  property ASSERT_ALWAYS_ON_EDGE_NOEDGE_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  test_expr;
  endproperty

  property ASSERT_ALWAYS_ON_EDGE_POSEDGE_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  ( (!sampling_event ##1 sampling_event)
    |-> test_expr );
  endproperty

  property ASSERT_ALWAYS_ON_EDGE_NEGEDGE_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  ( (sampling_event ##1 !sampling_event)
    |-> test_expr );
  endproperty

  property ASSERT_ALWAYS_ON_EDGE_ANYEDGE_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  ( ( (!sampling_event ##1 sampling_event) or
      (sampling_event ##1 !sampling_event) )
      |-> test_expr );
  endproperty


`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
    property ASSERT_ALWAYS_ON_EDGE_NOEDGE_TEST_EXPR_XZ_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    !$isunknown(test_expr);
    endproperty

    property ASSERT_ALWAYS_ON_EDGE_POSEDGE_SAMP_EVENT_0_XZ_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    ( ((!$past(sampling_event)) && $past(`OVL_RESET_SIGNAL == 1'b1)) 
      |-> !$isunknown(sampling_event) );
    endproperty

    property ASSERT_ALWAYS_ON_EDGE_POSEDGE_SAMP_EVENT_XZ_1_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    ( (($isunknown($past(sampling_event)) && (!$isunknown(sampling_event))) &&
      $past(`OVL_RESET_SIGNAL == 1'b1))
      |-> !sampling_event );
    endproperty

    property ASSERT_ALWAYS_ON_EDGE_SAMP_EVENT_XZ_XZ_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    ( (($isunknown(sampling_event)) && $past(`OVL_RESET_SIGNAL == 1'b1))
      |-> !$isunknown($past(sampling_event)) );
    endproperty

    property ASSERT_ALWAYS_ON_EDGE_POSEDGE_TEST_EXPR_XZ_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    ( ($rose(sampling_event) && $past(`OVL_RESET_SIGNAL == 1'b1))
      |-> !$isunknown(test_expr) );
    endproperty

    property ASSERT_ALWAYS_ON_EDGE_NEGEDGE_SAMP_EVENT_1_XZ_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    ( ($past(sampling_event) && $past(`OVL_RESET_SIGNAL == 1'b1))
      |-> !$isunknown(sampling_event) );
    endproperty

    property ASSERT_ALWAYS_ON_EDGE_NEGEDGE_SAMP_EVENT_XZ_0_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    ( (($isunknown($past(sampling_event)) && $past(`OVL_RESET_SIGNAL == 1'b1)) &&
       (!$isunknown(sampling_event)))
      |-> sampling_event );
    endproperty

    property ASSERT_ALWAYS_ON_EDGE_NEGEDGE_TEST_EXPR_XZ_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    ( ($fell(sampling_event) && $past(`OVL_RESET_SIGNAL == 1'b1))
      |-> !$isunknown(test_expr) );
    endproperty

    property ASSERT_ALWAYS_ON_EDGE_ANYEDGE_SAMP_EVENT_XZ_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    (!($isunknown(sampling_event)));
    endproperty

    property ASSERT_ALWAYS_ON_EDGE_ANYEDGE_PREV_SAMP_EVENT_XZ_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    ( ($isunknown($past(sampling_event)) && $past(`OVL_RESET_SIGNAL == 1'b1))
      |-> $isunknown(sampling_event) );
    endproperty

    property ASSERT_ALWAYS_ON_EDGE_ANYEDGE_TEST_EXPR_XZ_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    ( ((!$stable(sampling_event)) && $past(`OVL_RESET_SIGNAL == 1'b1))
      |-> !$isunknown(test_expr));
    endproperty

  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF


  generate

    case (property_type)
      `OVL_ASSERT_2STATE,
      `OVL_ASSERT: begin : ovl_assert
        if (edge_type == `OVL_NOEDGE) begin : a_assert_always_on_edge_noedge
          A_ASSERT_ALWAYS_ON_EDGE_NOEDGE_P:
          assert property (ASSERT_ALWAYS_ON_EDGE_NOEDGE_P)
          else ovl_error_t(`OVL_FIRE_2STATE,"Test expression is FALSE irrespective of sampling event");


`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
          A_ASSERT_ALWAYS_ON_EDGE_NOEDGE_TEST_EXPR_XZ_P:
          assert property (ASSERT_ALWAYS_ON_EDGE_NOEDGE_TEST_EXPR_XZ_P)
          else ovl_error_t(`OVL_FIRE_XCHECK,"test_expr contains X or Z");
  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF


        end

        if (edge_type == `OVL_POSEDGE) begin : a_assert_always_on_edge_posedge
          A_ASSERT_ALWAYS_ON_EDGE_POSEDGE_P:
          assert property (ASSERT_ALWAYS_ON_EDGE_POSEDGE_P)
          else ovl_error_t(`OVL_FIRE_2STATE,"Test expression is FALSE on posedge of sampling event");


`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
          A_ASSERT_ALWAYS_ON_EDGE_POSEDGE_TEST_EXPR_XZ_P:
          assert property (ASSERT_ALWAYS_ON_EDGE_POSEDGE_TEST_EXPR_XZ_P)
          else ovl_error_t(`OVL_FIRE_XCHECK,"test_expr contains X or Z");

          A_ASSERT_ALWAYS_ON_EDGE_POSEDGE_SAMP_EVENT_0_XZ_P:
          assert property (ASSERT_ALWAYS_ON_EDGE_POSEDGE_SAMP_EVENT_0_XZ_P)
          else ovl_error_t(`OVL_FIRE_XCHECK,"sampling_event contains X or Z");

          A_ASSERT_ALWAYS_ON_EDGE_POSEDGE_SAMP_EVENT_XZ_1_P:
          assert property (ASSERT_ALWAYS_ON_EDGE_POSEDGE_SAMP_EVENT_XZ_1_P)
          else ovl_error_t(`OVL_FIRE_XCHECK,"sampling_event contains X or Z");

          A_ASSERT_ALWAYS_ON_EDGE_SAMP_EVENT_XZ_XZ_P:
          assert property (ASSERT_ALWAYS_ON_EDGE_SAMP_EVENT_XZ_XZ_P)
          else ovl_error_t(`OVL_FIRE_XCHECK,"sampling_event contains X or Z");
  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF


        end

        if (edge_type == `OVL_NEGEDGE) begin : a_assert_always_on_edge_negedge
          A_ASSERT_ALWAYS_ON_EDGE_NEGEDGE_P:
          assert property (ASSERT_ALWAYS_ON_EDGE_NEGEDGE_P)
          else ovl_error_t(`OVL_FIRE_2STATE,"Test expression is FALSE on negedge of sampling event");


`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
          A_ASSERT_ALWAYS_ON_EDGE_NEGEDGE_TEST_EXPR_XZ_P:
          assert property (ASSERT_ALWAYS_ON_EDGE_NEGEDGE_TEST_EXPR_XZ_P)
          else ovl_error_t(`OVL_FIRE_XCHECK,"test_expr contains X or Z");

          A_ASSERT_ALWAYS_ON_EDGE_NEGEDGE_SAMP_EVENT_1_XZ_P:
          assert property (ASSERT_ALWAYS_ON_EDGE_NEGEDGE_SAMP_EVENT_1_XZ_P)
          else ovl_error_t(`OVL_FIRE_XCHECK,"sampling_event contains X or Z");

          A_ASSERT_ALWAYS_ON_EDGE_NEGEDGE_SAMP_EVENT_XZ_0_P:
          assert property (ASSERT_ALWAYS_ON_EDGE_NEGEDGE_SAMP_EVENT_XZ_0_P)
          else ovl_error_t(`OVL_FIRE_XCHECK," sampling_event contains X or Z ");

          A_ASSERT_ALWAYS_ON_EDGE_SAMP_EVENT_XZ_XZ_P:
          assert property (ASSERT_ALWAYS_ON_EDGE_SAMP_EVENT_XZ_XZ_P)
          else ovl_error_t(`OVL_FIRE_XCHECK,"sampling_event contains X or Z");
  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF


        end

        if (edge_type == `OVL_ANYEDGE) begin : a_assert_always_on_edge_anyedge
          A_ASSERT_ALWAYS_ON_EDGE_ANYEDGE_P:
          assert property (ASSERT_ALWAYS_ON_EDGE_ANYEDGE_P)
          else ovl_error_t(`OVL_FIRE_2STATE,"Test expression is FALSE on any edge of sampling event");


`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
          A_ASSERT_ALWAYS_ON_EDGE_ANYEDGE_TEST_EXPR_XZ_P:
          assert property (ASSERT_ALWAYS_ON_EDGE_ANYEDGE_TEST_EXPR_XZ_P)
          else ovl_error_t(`OVL_FIRE_XCHECK,"test_expr contains X or Z");

          A_ASSERT_ALWAYS_ON_EDGE_ANYEDGE_SAMP_EVENT_XZ_P:
          assert property (ASSERT_ALWAYS_ON_EDGE_ANYEDGE_SAMP_EVENT_XZ_P)
          else ovl_error_t(`OVL_FIRE_XCHECK,"sampling_event contains X or Z");

          A_ASSERT_ALWAYS_ON_EDGE_ANYEDGE_PREV_SAMP_EVENT_XZ_P:
          assert property (ASSERT_ALWAYS_ON_EDGE_ANYEDGE_PREV_SAMP_EVENT_XZ_P)
          else ovl_error_t(`OVL_FIRE_XCHECK,"sampling_event contains X or Z");
  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF


        end
      end
      `OVL_ASSUME_2STATE,
      `OVL_ASSUME: begin : ovl_assume
        if (edge_type == `OVL_NOEDGE) begin : m_assert_always_on_edge_noedge
          M_ASSERT_ALWAYS_ON_EDGE_NOEDGE_P:
          assume property (ASSERT_ALWAYS_ON_EDGE_NOEDGE_P);


`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
          M_ASSERT_ALWAYS_ON_EDGE_NOEDGE_TEST_EXPR_XZ_P:
          assume property (ASSERT_ALWAYS_ON_EDGE_NOEDGE_TEST_EXPR_XZ_P);
  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF


        end

        if (edge_type == `OVL_POSEDGE) begin : m_assert_always_on_edge_posedge
          M_ASSERT_ALWAYS_ON_EDGE_POSEDGE_P:
          assume property (ASSERT_ALWAYS_ON_EDGE_POSEDGE_P);


`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
          M_ASSERT_ALWAYS_ON_EDGE_POSEDGE_TEST_EXPR_XZ_P:
          assume property (ASSERT_ALWAYS_ON_EDGE_POSEDGE_TEST_EXPR_XZ_P);

          M_ASSERT_ALWAYS_ON_EDGE_POSEDGE_SAMP_EVENT_0_XZ_P:
          assume property (ASSERT_ALWAYS_ON_EDGE_POSEDGE_SAMP_EVENT_0_XZ_P);

          M_ASSERT_ALWAYS_ON_EDGE_POSEDGE_SAMP_EVENT_XZ_1_P:
          assume property (ASSERT_ALWAYS_ON_EDGE_POSEDGE_SAMP_EVENT_XZ_1_P);

          M_ASSERT_ALWAYS_ON_EDGE_SAMP_EVENT_XZ_XZ_P:
          assume property (ASSERT_ALWAYS_ON_EDGE_SAMP_EVENT_XZ_XZ_P);
  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF


        end

        if (edge_type == `OVL_NEGEDGE) begin : m_assert_always_on_edge_negedge
          M_ASSERT_ALWAYS_ON_EDGE_NEGEDGE_P:
          assume property (ASSERT_ALWAYS_ON_EDGE_NEGEDGE_P);


`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
          M_ASSERT_ALWAYS_ON_EDGE_NEGEDGE_TEST_EXPR_XZ_P:
          assume property (ASSERT_ALWAYS_ON_EDGE_NEGEDGE_TEST_EXPR_XZ_P);

          M_ASSERT_ALWAYS_ON_EDGE_NEGEDGE_SAMP_EVENT_1_XZ_P:
          assume property (ASSERT_ALWAYS_ON_EDGE_NEGEDGE_SAMP_EVENT_1_XZ_P);

          M_ASSERT_ALWAYS_ON_EDGE_NEGEDGE_SAMP_EVENT_XZ_0_P:
          assume property (ASSERT_ALWAYS_ON_EDGE_NEGEDGE_SAMP_EVENT_XZ_0_P);

          M_ASSERT_ALWAYS_ON_EDGE_SAMP_EVENT_XZ_XZ_P:
          assume property (ASSERT_ALWAYS_ON_EDGE_SAMP_EVENT_XZ_XZ_P);
  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF


        end

        if (edge_type == `OVL_ANYEDGE) begin : m_assert_always_on_edge_anyedge
          M_ASSERT_ALWAYS_ON_EDGE_ANYEDGE_P:
          assume property (ASSERT_ALWAYS_ON_EDGE_ANYEDGE_P);


`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
          M_ASSERT_ALWAYS_ON_EDGE_ANYEDGE_TEST_EXPR_XZ_P:
          assume property (ASSERT_ALWAYS_ON_EDGE_ANYEDGE_TEST_EXPR_XZ_P);

          M_ASSERT_ALWAYS_ON_EDGE_ANYEDGE_SAMP_EVENT_XZ_P:
          assume property (ASSERT_ALWAYS_ON_EDGE_ANYEDGE_SAMP_EVENT_XZ_P);

          M_ASSERT_ALWAYS_ON_EDGE_ANYEDGE_PREV_SAMP_EVENT_XZ_P:
          assume property (ASSERT_ALWAYS_ON_EDGE_ANYEDGE_PREV_SAMP_EVENT_XZ_P);
  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF


        end
      end
      `OVL_IGNORE : begin : ovl_ignore
        // do nothing;
      end
      default     : initial ovl_error_t(`OVL_FIRE_2STATE,"");
    endcase

  endgenerate

`endif // OVL_ASSERT_ON

