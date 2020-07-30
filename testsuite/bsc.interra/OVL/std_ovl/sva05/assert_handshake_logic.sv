// Accellera Standard V2.8.1 Open Verification Library (OVL).
// Accellera Copyright (c) 2005-2014. All rights reserved.



`ifdef OVL_ASSERT_ON

  reg first_req;

  always @ (posedge clk) begin
    if (`OVL_RESET_SIGNAL != 1'b0) begin
      if((first_req ^ first_req) == 1'b0) begin
        if (req)
          first_req <= 1'b1;
        end
        else begin
          first_req <= 1'b0;
        end
      end
    else
      first_req <= 1'b0;
  end

  property ASSERT_HANDSHAKE_ACK_MIN_CYCLE_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  $rose(req) |-> (!($rose(ack))) [*min_ack_cycle];
  endproperty

  property ASSERT_HANDSHAKE_ACK_MAX_CYCLE_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  $rose(req) && (!$rose(ack)) |->
  (##[1:(max_ack_cycle > 0 ? max_ack_cycle : 2)] ($rose(ack) || ($rose(req) && (req_drop == 1'b1))));
  endproperty

  property ASSERT_HANDSHAKE_ACK_MAX_LENGTH_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  $rose(ack) |-> (ack)[*1:(max_ack_length > 0 ? max_ack_length : 2) ] ##1 (!ack);
  endproperty

  property ASSERT_HANDSHAKE_REQ_DROP_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  $rose(req) |-> (req[*1:$]) ##0 $rose(ack);
  endproperty

  property ASSERT_HANDSHAKE_MULTIPLE_REQ_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  not (($rose(req) && !ack) ##1 (req && !ack) [*0:$]
  ##1 (!req && !ack) [*1:$] ##1 ($rose(req)));
  endproperty

  property ASSERT_HANDSHAKE_REQ_DEASSERT_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  ($rose(ack) && (req)) |-> (##[0:deassert_count](!req));
  endproperty

  property ASSERT_HANDSHAKE_ACK_WITHOUT_REQ_FIRST_REQ_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  $rose(ack) |-> (first_req || req);
  endproperty

  property ASSERT_HANDSHAKE_ACK_WITHOUT_REQ_SUBSEQUENT_REQ_P;
  @(posedge clk)
  disable iff (`OVL_RESET_SIGNAL != 1'b1)
  $fell(ack) |-> $rose(req) within (!ack [*0:$] ##1 ack);
  endproperty

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
    property ASSERT_HANDSHAKE_REQ_XZ_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    !$isunknown( req );
    endproperty

    property ASSERT_HANDSHAKE_ACK_XZ_P;
    @(posedge clk)
    disable iff (`OVL_RESET_SIGNAL != 1'b1)
    !$isunknown( ack );
    endproperty
  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF

  generate

    case (property_type)
      `OVL_ASSERT_2STATE,
      `OVL_ASSERT: begin : ovl_assert
        if (min_ack_cycle > 0) begin : a_assert_handshake_ack_min_cycle
          A_ASSERT_HANDSHAKE_ACK_MIN_CYCLE_P:
          assert property (ASSERT_HANDSHAKE_ACK_MIN_CYCLE_P)
          else ovl_error_t(`OVL_FIRE_2STATE,"Acknowledge asserted before elapse of specified minimum min_ack_cycle cycles from request");
        end
        if (max_ack_cycle > 0) begin : a_assert_handshake_ack_max_cycle
          A_ASSERT_HANDSHAKE_ACK_MAX_CYCLE_P:
          assert property (ASSERT_HANDSHAKE_ACK_MAX_CYCLE_P)
          else ovl_error_t(`OVL_FIRE_2STATE,"Acknowledge is not asserted within specified maximum max_ack_cycle cycles from request");
        end
        if ((max_ack_length >= 1)) begin : a_assert_handshake_ack_max_length
          A_ASSERT_HANDSHAKE_ACK_MAX_LENGTH_P:
          assert property (ASSERT_HANDSHAKE_ACK_MAX_LENGTH_P)
          else ovl_error_t(`OVL_FIRE_2STATE,"Duration of continuous asserted state of acknowledge violates specified maximum ack_max_length cycles");
        end
        if (deassert_count > 0) begin : a_assert_handshake_req_deassert
          A_ASSERT_HANDSHAKE_REQ_DEASSERT_P:
          assert property (ASSERT_HANDSHAKE_REQ_DEASSERT_P)
          else ovl_error_t(`OVL_FIRE_2STATE,"Duration of continuous asserted state of request violates specified deassert_count cycles");
        end
        if (req_drop > 0) begin : a_assert_handshake_req_drop
          A_ASSERT_HANDSHAKE_REQ_DROP_P:
          assert property (ASSERT_HANDSHAKE_REQ_DROP_P)
          else ovl_error_t(`OVL_FIRE_2STATE,"Request is deasserted before acknowledgement arrives");
        end
        A_ASSERT_HANDSHAKE_MULTIPLE_REQ_P:
        assert property (ASSERT_HANDSHAKE_MULTIPLE_REQ_P)
        else ovl_error_t(`OVL_FIRE_2STATE,"New request arrives before previous request is acknowledged");
        A_ASSERT_HANDSHAKE_ACK_WITHOUT_REQ_FIRST_REQ_P:
        assert property (ASSERT_HANDSHAKE_ACK_WITHOUT_REQ_FIRST_REQ_P)
          else ovl_error_t(`OVL_FIRE_2STATE,"Acknowledge arrives without a pending request");
        A_ASSERT_HANDSHAKE_ACK_WITHOUT_REQ_SUBSEQUENT_REQ_P:
        assert property (ASSERT_HANDSHAKE_ACK_WITHOUT_REQ_SUBSEQUENT_REQ_P)
          else ovl_error_t(`OVL_FIRE_2STATE,"Acknowledge arrives without a pending request");

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
        //x/z checking for req signal

        A_ASSERT_HANDSHAKE_REQ_XZ_P:
        assert property (ASSERT_HANDSHAKE_REQ_XZ_P)
        else ovl_error_t(`OVL_FIRE_XCHECK,"req contains X or Z");

        //x/z checking for ack signal

        A_ASSERT_HANDSHAKE_ACK_XZ_P:
        assert property (ASSERT_HANDSHAKE_ACK_XZ_P)
        else ovl_error_t(`OVL_FIRE_XCHECK,"ack contains X or Z");

  `endif // OVL_IMPLICIT_XCHECK_OFF
`endif // OVL_XCHECK_OFF


      end
      `OVL_ASSUME_2STATE,
      `OVL_ASSUME: begin : ovl_assume
        if (min_ack_cycle > 0) begin : m_assert_handshake_ack_min_cycle
          M_ASSERT_HANDSHAKE_ACK_MIN_CYCLE_P:
          assume property (ASSERT_HANDSHAKE_ACK_MIN_CYCLE_P);
        end
        if (max_ack_cycle > 0) begin : m_assert_handshake_ack_max_cycle
          M_ASSERT_HANDSHAKE_ACK_MAX_CYCLE_P:
          assume property (ASSERT_HANDSHAKE_ACK_MAX_CYCLE_P);
        end
        if ((max_ack_length >= 1)) begin : m_assert_handshake_ack_max_length
          M_ASSERT_HANDSHAKE_ACK_MAX_LENGTH_P:
          assume property (ASSERT_HANDSHAKE_ACK_MAX_LENGTH_P);
        end
        if (deassert_count > 0) begin : m_assert_handshake_req_deassert
          M_ASSERT_HANDSHAKE_REQ_DEASSERT_P:
          assume property (ASSERT_HANDSHAKE_REQ_DEASSERT_P);
        end
        if (req_drop > 0) begin : m_assert_handshake_req_drop_p
          M_ASSERT_HANDSHAKE_REQ_DROP_P:
          assume property (ASSERT_HANDSHAKE_REQ_DROP_P);
        end
        M_ASSERT_HANDSHAKE_MULTIPLE_REQ_P:
        assume property (ASSERT_HANDSHAKE_MULTIPLE_REQ_P);
        M_ASSERT_HANDSHAKE_ACK_WITHOUT_REQ_FIRST_REQ_P:
        assume property (ASSERT_HANDSHAKE_ACK_WITHOUT_REQ_FIRST_REQ_P);
        M_ASSERT_HANDSHAKE_ACK_WITHOUT_REQ_SUBSEQUENT_REQ_P:
        assume property (ASSERT_HANDSHAKE_ACK_WITHOUT_REQ_SUBSEQUENT_REQ_P);

`ifdef OVL_XCHECK_OFF
  //Do nothing
`else
  `ifdef OVL_IMPLICIT_XCHECK_OFF
    //Do nothing
  `else
        //x/z checking for req signal

        M_ASSERT_HANDSHAKE_REQ_XZ_P:
        assume property (ASSERT_HANDSHAKE_REQ_XZ_P);

        //x/z checking for ack signal

        M_ASSERT_HANDSHAKE_ACK_XZ_P:
        assume property (ASSERT_HANDSHAKE_ACK_XZ_P);

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

     cover_req_asserted:
     cover property (@(posedge clk) ((`OVL_RESET_SIGNAL != 1'b0) && $rose(req)))
                     ovl_cover_t("req_asserted covered");

     cover_ack_asserted:
     cover property (@(posedge clk) ((`OVL_RESET_SIGNAL != 1'b0) && $rose(ack)))
                     ovl_cover_t("ack_asserted covered");
    end
   end

  endgenerate

`endif // OVL_COVER_ON

