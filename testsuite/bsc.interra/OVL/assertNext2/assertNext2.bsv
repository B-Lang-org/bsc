/*************************************************************************************************************
Assertion-Checker: assert_next

Description: test_expr is not TRUE a specified no. of clock cycles after the start_event is asserted.

Status: simulation should fail

Author: pktiwari@noida.interrasystems.com

Date: 02-17-2006 

*************************************************************************************************************/

import OVLAssertions ::*;

typedef enum {First_State, Second_State, Third_State, Fourth_State, Fifth_State} FSM_State deriving (Eq, Bits);

(* synthesize *)
module assertNext2 (Empty);

Reg#(FSM_State) state <- mkRegA(First_State);
   
Reg#(Bool) test_expr <- mkRegA(False);

let defaults = mkOVLDefaults;
defaults.num_cks = 2; //num_cks : 2
AssertStartTest_IFC#(Bool) assertNex <- bsv_assert_next(defaults);
   
rule test(True);
    assertNex.start(state == Second_State);//start_event : Second_State
    assertNex.test(test_expr);             //test_expr : test_expr
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
	end
	Third_State:
	begin
	    state <= Fourth_State;
	end
	Fourth_State:
	begin
	    state <= Fifth_State;
		test_expr <= True;		
	end
	Fifth_State:
	begin
	    state <= First_State;
		test_expr <= False;		
	    $finish(0);
	end
    endcase
endrule
endmodule
