/*************************************************************************************************************
Assertion-Checker: assert_change

Description: after the start_event is asserted, the test_expr changes value within the num_cks no. of clock cycles. 

Status: simulation should pass

Author: pktiwari@noida.interrasystems.com

Date: 02-17-2006 

*************************************************************************************************************/

import OVLAssertions::*;

typedef enum {First_State, Second_State, Third_State, Fourth_State, Fifth_State} FSM_State deriving (Eq, Bits);

(* synthesize *)
module assertChange1 (Empty);

Reg#(FSM_State) state <- mkRegA(First_State);
Reg#(Bit#(3)) test_expr <- mkRegA(0);

let defaults = mkOVLDefaults;
defaults.num_cks = 2;//num_cks : 2

AssertStartTest_IFC#(Bit#(3)) assertChange <- bsv_assert_change(defaults);   

rule test(True);
    assertChange.start(state == Second_State);//start_event : Second_State
    assertChange.test(test_expr); //test_expr : test_expr
endrule

rule every (True);
    case (state)
    First_State:
	begin
	    state <= Second_State;
	 end
	 Second_State:
	 begin
	    state <= Third_State;
		test_expr  <= 3'b010;
	 end
	 Third_State:
	 begin
	    state <= Fourth_State;
	 end
	 Fourth_State:
	 begin
	    state <= Fifth_State;
		test_expr <= 3'b001;
	 end
	 Fifth_State:
	 begin
	    state <= First_State;
	    $finish(0);
	 end
     endcase
endrule
endmodule
