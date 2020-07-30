/*************************************************************************************************************
Assertion-Checker: assert_no_transition

Description: test_expr doesn't transition from start_state to next_state. 

Status: simulation should pass

Author: pktiwari@noida.interrasystems.com

Date: 03-06-2006 

*************************************************************************************************************/

import OVLAssertions::*;

typedef enum {First_State, Second_State, Third_State, Fourth_State, Fifth_State, Sixth_State, Seventh_State} FSM_State deriving (Eq, Bits);

(* synthesize *)
module assertNoTransition1 (Empty);

Reg#(FSM_State) state <- mkRegA(First_State);
Reg#(Bit#(3)) test_expr <- mkRegA(0);

let defaults = mkOVLDefaults;

AssertTransitionTest_IFC#(Bit#(3)) assertNoTran <- bsv_assert_no_transition(defaults);   

rule test(True);
    assertNoTran.test(test_expr);//test_expr : test_expr 
	assertNoTran.start(3'b010); //start_state : 3'b010
	assertNoTran.next(3'b100); //next_state : 3'b100
	
endrule

rule every (True);
    case (state)
    First_State:
	begin
	    state <= Second_State;
		test_expr  <= 3'b100;
	end
	Second_State:
	begin
	    state <= Third_State;
		test_expr  <= 3'b010;
	end
	Third_State:
	begin
	    state <= Fourth_State;
		test_expr  <= 3'b011;
	end
	Fourth_State:
	begin
	    state <= Fifth_State;
		test_expr <= 3'b100;
	end
	Fifth_State:
	begin
	    state <= Sixth_State;
		test_expr  <= 3'b110;
	end
	Sixth_State:
	begin
	     state <= Seventh_State;
	end
	Seventh_State:
	begin
	    state <= First_State;
	    $finish(0);
	end	
    endcase
endrule
endmodule
