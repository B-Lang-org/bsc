package Design_0;

typedef enum {SHW, SMRW, IMRW, DMRW, OTHERS} SnoopType
    deriving (Bits, Eq);

typedef enum {Dirty, Shared, Invalid, X}  StateType
    deriving (Bits, Eq);

interface Design_in_IFC;

    method Action       start(
                              Bit#(1)   r_wb,
                              SnoopType snoop_type_in, 
                              Bit#(1)   is_snoop,
                              Bit#(1)   info_avail,
                              Bit#(1)   invalidate,
                              Bit#(1)   all_shared,
                              Bit#(1)   mem_served,
                              Bit#(1)   bus_ack
                             );
    method SnoopType    snoop_type_out(
                                       Bit#(1) h_mb, 
                                       Bit#(1) r_wb
                                      );
    method Bit#(1)      is_shared();
    method StateType    cont_state(); 

endinterface:  Design_in_IFC

/*Here in the below function used the mapping 

  Shared    = 01
  Dirty     = 00
  Invalid   = 10
  X         = 11

*/

function SnoopType deter_snoop_type(StateType f_state, Bit#(1) f_hmb, Bit#(1) f_rwb);
SnoopType stype;
    case ({pack(f_state), f_hmb, f_rwb}) 
        {2'b01, 1'b1, 1'b0}:  stype = SHW;
        {2'b01, 1'b0, 1'b_}:  stype = SMRW;
        {2'b10, 1'b0, 1'b_}:  stype = IMRW;
        {2'b00, 1'b0, 1'b_}:  stype = DMRW;
        default            :  stype = OTHERS;
    endcase
    return stype;
endfunction: deter_snoop_type 

(*
    always_ready,
    always_enabled,
    clock_prefix = "clk",
    reset_prefix = "reset"
*)
module mkDesign_in(Design_in_IFC);

    Reg#(StateType) state();
    mkReg#(Invalid) the_state(state);

    method Action start(
                        Bit#(1)     r_wb, 
                        SnoopType   snoop_type_in, 
                        Bit#(1)     is_snoop, 
                        Bit#(1)     info_avail, 
                        Bit#(1)     invalidate, 
                        Bit#(1)     all_shared, 
                        Bit#(1)     mem_served, 
                        Bit#(1)     bus_ack
                       );
        action
            case ({is_snoop, bus_ack, pack(snoop_type_in), pack(state), r_wb, info_avail, invalidate})
                {1'b1, 1'b0, 3'b000, 2'b01, 1'b_, 1'b1, 1'b_}: state <= Invalid;
                {1'b1, 1'b0, 3'b001, 2'b00, 1'b_, 1'b1, 1'b0}: state <= Shared;
                {1'b1, 1'b0, 3'b001, 2'b00, 1'b_, 1'b1, 1'b1}: state <= Invalid;
                {1'b1, 1'b0, 3'b010, 2'b01, 1'b_, 1'b1, 1'b1}: state <= Invalid;
                {1'b1, 1'b0, 3'b010, 2'b00, 1'b_, 1'b1, 1'b0}: state <= Shared;
                {1'b1, 1'b0, 3'b010, 2'b00, 1'b_, 1'b1, 1'b1}: state <= Invalid;
                {1'b1, 1'b0, 3'b011, 2'b01, 1'b_, 1'b1, 1'b1}: state <= Invalid;
                {1'b1, 1'b0, 3'b011, 2'b00, 1'b_, 1'b1, 1'b0}: state <= Shared;
                {1'b1, 1'b0, 3'b011, 2'b00, 1'b_, 1'b1, 1'b1}: state <= Invalid;
                {1'b1, 1'b0, 3'b001, 2'b01, 1'b_, 1'b0, 1'b0}: if (all_shared == 0) state <=  Dirty; else state <= state;
                {1'b1, 1'b1, 3'b010, 2'b__, 1'b1, 1'b_, 1'b_}: if (mem_served == 1) state <=  Dirty; else state <= Shared;
                {1'b1, 1'b1, 3'b011, 2'b__, 1'b1, 1'b_, 1'b_}: if (mem_served == 1) state <=  Dirty; else state <= Shared;
                {1'b0, 1'b_, 3'b___, 2'b__, 1'b_, 1'b_, 1'b_}: state <= state;
                default                                      : state <= state;
            endcase
        endaction
     endmethod: start     
                      
     method SnoopType snoop_type_out(Bit#(1) h_mb, Bit#(1) r_wb);
        snoop_type_out =  deter_snoop_type(state, h_mb, r_wb);
     endmethod: snoop_type_out

     method Bit#(1) is_shared();
        is_shared = ((state==Shared)? 1 : 0);
     endmethod: is_shared

     method StateType cont_state(); 
        cont_state = state;
     endmethod: cont_state 
endmodule: mkDesign_in
endpackage : Design_0
