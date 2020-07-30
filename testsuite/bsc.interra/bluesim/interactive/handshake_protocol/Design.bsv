package Design;

typedef enum {IDLE, REQUEST, ACQUISITION} HSstates
          deriving (Eq,Bits);  

interface Design_IFC;
    method Action setInput (Bit#(1) ack); 
    method Bit#(1) req();
    method Bit#(1) start();
    method Bit#(1) valid();
    method Bit#(1) done(); 
endinterface: Design_IFC

(*
       CLK = "clk",
       RST_N = "reset"
*)

module mkDesign (Design_IFC);

  Reg#(HSstates)    state();
  mkReg#(IDLE)      t_state(state);

  Reg#(Bit#(1))     req_reg();
  mkReg#(0)         t_req_reg(req_reg);
  
  Reg#(Bit#(1))     start_reg();
  mkReg#(0)         t_start_reg(start_reg);
  
  Reg#(Bit#(1))     valid_reg();
  mkReg#(0)         t_valid_reg(valid_reg);
  
  Reg#(Bit#(1))     done_reg();
  mkReg#(1)         t_done_reg(done_reg);
  
  Reg#(Bit#(2))     counter();
  mkReg#(0)         t_counter(counter);

  RWire#(Bit#(1))   ack1();
  mkRWire           t_ack1(ack1);

  rule fromIdle (state == IDLE);
    begin
        req_reg   <= 1;
        state     <= REQUEST;
        counter   <= 0;
        done_reg  <= 0;
    end
  endrule

  rule fromRequest (state == REQUEST);
    begin
        if (ack1.wget == Just( 1 )) begin
            req_reg     <= 0;
            start_reg   <= 1;
            state       <= ACQUISITION;
            valid_reg   <= 1;
        end 
    end
  endrule

  rule fromAcquisition (state == ACQUISITION);
    if (counter == 3) begin
        counter     <= counter + 1;
        done_reg    <= 1;
        valid_reg   <= 0;
        state       <= IDLE;
        req_reg     <= 0;
        start_reg   <= 0;
    end else begin
        counter     <= counter + 1;
        valid_reg   <= 1;
        req_reg     <= 0;
        start_reg   <= 0;
    end
  endrule

  method req();
     req = req_reg;
  endmethod: req

  method start();
     start = start_reg;
  endmethod: start

  method valid();
     valid = valid_reg;
  endmethod: valid

  method done();
     done = done_reg;
  endmethod: done

  method Action setInput (ack) if(state == REQUEST);
        ack1.wset( ack ) ;
  endmethod: setInput


endmodule: mkDesign

endpackage: Design
