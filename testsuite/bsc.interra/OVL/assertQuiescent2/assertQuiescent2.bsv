/*************************************************************************************************************
Assertion-Checker: assert_quiescent_state

Description: sample_event occurs and test_expr doesn't equal the check_value. 

Status: simulation should fail

Author: pktiwari@noida.interrasystems.com

Date: 03-06-2006 

*************************************************************************************************************/

import OVLAssertions::*;

typedef enum {First_State, Second_State, Third_State, Fourth_State, Fifth_State} FSM_State deriving (Eq, Bits);

(* synthesize *)
module assertQuiescent2 (Empty);

Reg#(FSM_State) state <- mkRegA(First_State);
Reg#(Bit#(3)) state_expr <- mkRegA(0);

let defaults = mkOVLDefaults;

AssertQuiescentTest_IFC#(Bit#(3)) assertQuies <- bsv_assert_quiescent_state(defaults);   

rule test(True);
    assertQuies.sample(state == Third_State); //sample_event : state == Third_State
	assertQuies.state(state_expr);//test_expr : test_expr
	assertQuies.check(3'b011);//check_value
	
endrule

rule every (True);
    case (state)
    First_State:
	begin
	    state <= Second_State;
		state_expr  <= 3'b100;
	 end
	 Second_State:
	 begin
	    state <= Third_State;
		state_expr  <= 3'b010;
	 end
	 Third_State:
	 begin
	    state <= Fourth_State;
		state_expr  <= 3'b011;
	 end
	 Fourth_State:
	 begin
	    state <= Fifth_State;
		state_expr <= 3'b100;
	 end
	 Fifth_State:
	 begin
	    state <= First_State;
		state_expr  <= 3'b110;
	    $finish(0);
	 end
     endcase
endrule
endmodule
