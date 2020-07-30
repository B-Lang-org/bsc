// Accellera Standard V2.8.1 Open Verification Library (OVL).
// Accellera Copyright (c) 2005-2014. All rights reserved.

`ifdef OVL_SHARED_CODE

  parameter NC0 = (necessary_condition == `OVL_TRIGGER_ON_MOST_PIPE);
  parameter NC1 = (necessary_condition == `OVL_TRIGGER_ON_FIRST_PIPE);
  parameter NC2 = (necessary_condition == `OVL_TRIGGER_ON_FIRST_NOPIPE);
  parameter NUM_CKS_1 = (num_cks-1);
  parameter NUM_CKS_2 = (NUM_CKS_1 > 0) ? (NUM_CKS_1 - 1) : 0;

  reg [NUM_CKS_1:0]  seq_queue;

`ifdef OVL_SYNTHESIS
`else
  initial begin
    seq_queue = {num_cks{1'b0}};
  end
`endif

  always @ (posedge clk) begin
    if (`OVL_RESET_SIGNAL != 1'b1) begin
      seq_queue <= {num_cks{1'b0}};
    end
    else begin
      seq_queue[NUM_CKS_1] <= NC2 ? (~(|seq_queue[NUM_CKS_1:1]))
                                    && event_sequence[NUM_CKS_1] :
                                    event_sequence[NUM_CKS_1];
      seq_queue[NUM_CKS_2:0] <= (seq_queue >> 1) & event_sequence[NUM_CKS_2:0];
    end
  end

`endif // OVL_SHARED_CODE

`ifdef OVL_ASSERT_ON

  property ASSERT_SEQUENCE_TRIGGER_ON_FIRST_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
      not (&((seq_queue[NUM_CKS_1:1] & event_sequence[NUM_CKS_2:0]) |
           ~(seq_queue[NUM_CKS_1:1]))) != 1'b1;
  endproperty

  property ASSERT_SEQUENCE_TRIGGER_ON_MOST_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    seq_queue[1] |-> event_sequence[0];
  endproperty


`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
    property ASSERT_SEQUENCE_TRIGGER_ON_NC0_NC1_FIRST_EVENT_XZ_P;
      @(posedge clk)
      disable iff (`OVL_RESET_SIGNAL != 1'b1)
      !$isunknown(event_sequence[NUM_CKS_1]);
    endproperty

    property ASSERT_SEQUENCE_TRIGGER_ON_NC2_FIRST_EVENT_XZ_P;
      @(posedge clk)
      disable iff (`OVL_RESET_SIGNAL != 1'b1)
      ((!(|seq_queue[NUM_CKS_1:1])) || $isunknown((|seq_queue[NUM_CKS_1:1]))) |->
      !$isunknown(event_sequence[NUM_CKS_1]);
    endproperty

    property ASSERT_SEQUENCE_TRIGGER_ON_NC1_NC2_SUBSEQUENT_EVENTS_XZ_P;
      @(posedge clk)
      disable iff (`OVL_RESET_SIGNAL != 1'b1)
      !$isunknown((^(seq_queue[NUM_CKS_1:1] & event_sequence[NUM_CKS_2:0])));
    endproperty

    property ASSERT_SEQUENCE_TRIGGER_ON_NC0_NON_LAST_EVENTS_XZ_P;
      @(posedge clk)
      disable iff (`OVL_RESET_SIGNAL != 1'b1)
      !$isunknown((^(seq_queue[NUM_CKS_1:1] & event_sequence[NUM_CKS_2:0] &
                {{(NUM_CKS_2){1'b1}},{1'b0}})));
    endproperty

    property ASSERT_SEQUENCE_TRIGGER_ON_NC0_LAST_EVENT_XZ_1_XZ_P;
      @(posedge clk)
      disable iff (`OVL_RESET_SIGNAL != 1'b1)
      $isunknown(seq_queue[1]) |->
      !( $isunknown(event_sequence[0]) || event_sequence[0] );
    endproperty

    property ASSERT_SEQUENCE_TRIGGER_ON_NC0_LAST_EVENT_1_XZ_P;
      @(posedge clk)
      disable iff (`OVL_RESET_SIGNAL != 1'b1)
      (!$isunknown(seq_queue[1])) |->
      !(seq_queue[1] && $isunknown(event_sequence[0]));
    endproperty
  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

  generate

    case (property_type)
      `OVL_ASSERT_2STATE,
      `OVL_ASSERT: begin : ovl_assert
        if (NC0) begin : a_assert_sequence_trigger_on_most
          A_ASSERT_SEQUENCE_TRIGGER_ON_MOST_P:
          assert property (ASSERT_SEQUENCE_TRIGGER_ON_MOST_P)
          else ovl_error_t(`OVL_FIRE_2STATE,"First num_cks-1 events occured but they are not followed by the last event in sequence");
        end
        if (NC1 || NC2) begin : a_assert_sequence_trigger_on_first
          A_ASSERT_SEQUENCE_TRIGGER_ON_FIRST_P:
          assert property (ASSERT_SEQUENCE_TRIGGER_ON_FIRST_P)
          else ovl_error_t(`OVL_FIRE_2STATE,"First event occured but it is not followed by the rest of the events in sequence");
        end

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
        if (NC0 || NC1)
          begin : a_assert_sequence_trigger_on_nc0_nc1_first_event_xz
            A_ASSERT_SEQUENCE_TRIGGER_ON_NC0_NC1_FIRST_EVENT_XZ_P:
            assert property (ASSERT_SEQUENCE_TRIGGER_ON_NC0_NC1_FIRST_EVENT_XZ_P)
            else ovl_error_t(`OVL_FIRE_XCHECK,"First event in the sequence contains X or Z");
          end

        if (NC2)
          begin : a_assert_sequence_trigger_on_nc2_first_event_xz
            A_ASSERT_SEQUENCE_TRIGGER_ON_NC2_FIRST_EVENT_XZ_P:
            assert property (ASSERT_SEQUENCE_TRIGGER_ON_NC2_FIRST_EVENT_XZ_P)
            else ovl_error_t(`OVL_FIRE_XCHECK,"First event in the sequence contains X or Z");
          end

        if ( NC1 || NC2 )
          begin : a_assert_sequence_trigger_on_nc1_nc2_subsequent_events_xz
            A_ASSERT_SEQUENCE_TRIGGER_ON_NC1_NC2_SUBSEQUENT_EVENTS_XZ_P:
            assert property (ASSERT_SEQUENCE_TRIGGER_ON_NC1_NC2_SUBSEQUENT_EVENTS_XZ_P)
            else ovl_error_t(`OVL_FIRE_XCHECK,"Subsequent events in the sequence contain X or Z");
          end

        if ( NC0 )
          begin : a_assert_sequence_trigger_on_nc0_xz
            A_ASSERT_SEQUENCE_TRIGGER_ON_NC0_NON_LAST_EVENTS_XZ_P:
            assert property (ASSERT_SEQUENCE_TRIGGER_ON_NC0_NON_LAST_EVENTS_XZ_P)
            else ovl_error_t(`OVL_FIRE_XCHECK,"First num_cks-1 events in the sequence contain X or Z");

            A_ASSERT_SEQUENCE_TRIGGER_ON_NC0_LAST_EVENT_1_XZ_P:
            assert property (ASSERT_SEQUENCE_TRIGGER_ON_NC0_LAST_EVENT_1_XZ_P)
            else ovl_error_t(`OVL_FIRE_XCHECK,"Last event in the sequence contains X or Z");

            A_ASSERT_SEQUENCE_TRIGGER_ON_NC0_LAST_EVENT_XZ_1_XZ_P:
            assert property (ASSERT_SEQUENCE_TRIGGER_ON_NC0_LAST_EVENT_XZ_1_XZ_P)
            else ovl_error_t(`OVL_FIRE_XCHECK,"First num_cks-1 events in the sequence contain X or Z");
          end
 `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

      end
      `OVL_ASSUME_2STATE,
      `OVL_ASSUME: begin : ovl_assume
        if (NC0) begin : m_assert_sequence_trigger_on_most
          M_ASSERT_SEQUENCE_TRIGGER_ON_MOST_P:
          assume property (ASSERT_SEQUENCE_TRIGGER_ON_MOST_P);
        end
        if (NC1 || NC2) begin : m_assert_sequence_trigger_on_first
          M_ASSERT_SEQUENCE_TRIGGER_ON_FIRST_P:
          assume property (ASSERT_SEQUENCE_TRIGGER_ON_FIRST_P);
        end

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
        if (NC0 || NC1)
          begin : m_assert_sequence_trigger_on_nc0_nc1_first_event_xz
            M_ASSERT_SEQUENCE_TRIGGER_ON_NC0_NC1_FIRST_EVENT_XZ_P:
            assume property (ASSERT_SEQUENCE_TRIGGER_ON_NC0_NC1_FIRST_EVENT_XZ_P);
          end

        if (NC2)
          begin : m_assert_sequence_trigger_on_nc2_first_event_xz
            M_ASSERT_SEQUENCE_TRIGGER_ON_NC2_FIRST_EVENT_XZ_P:
            assume property (ASSERT_SEQUENCE_TRIGGER_ON_NC2_FIRST_EVENT_XZ_P);
          end

        if ( NC1 || NC2 )
          begin : m_assert_sequence_trigger_on_nc1_nc2_subsequent_events_xz
            M_ASSERT_SEQUENCE_TRIGGER_ON_NC1_NC2_SUBSEQUENT_EVENTS_XZ_P:
            assume property (ASSERT_SEQUENCE_TRIGGER_ON_NC1_NC2_SUBSEQUENT_EVENTS_XZ_P);
          end

        if ( NC0 )
          begin : m_assert_sequence_trigger_on_nc0_xz
            M_ASSERT_SEQUENCE_TRIGGER_ON_NC0_NON_LAST_EVENTS_XZ_P:
            assume property (ASSERT_SEQUENCE_TRIGGER_ON_NC0_NON_LAST_EVENTS_XZ_P);

            M_ASSERT_SEQUENCE_TRIGGER_ON_NC0_LAST_EVENT_1_XZ_P:
            assume property (ASSERT_SEQUENCE_TRIGGER_ON_NC0_LAST_EVENT_1_XZ_P);

            M_ASSERT_SEQUENCE_TRIGGER_ON_NC0_LAST_EVENT_XZ_1_XZ_P:
            assume property (ASSERT_SEQUENCE_TRIGGER_ON_NC0_LAST_EVENT_XZ_1_XZ_P);
          end
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
     if (OVL_COVER_BASIC_ON) begin : ovl_cover_basic

      cover_sequence_trigger:
      cover property (@(posedge clk)
                      ((`OVL_RESET_SIGNAL != 1'b0) &&
                      (((NC1 || NC2) && event_sequence[NUM_CKS_1]) ||
                      (NC0 && &seq_queue[1]))))
                     ovl_cover_t("sequence_trigger covered");
     end
    end

  endgenerate

`endif // OVL_COVER_ON
