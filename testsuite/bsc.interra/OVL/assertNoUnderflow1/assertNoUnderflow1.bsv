/*************************************************************************************************************
Assertion-Checker: assert_no_underflow

Description: test_expr doesn't underflow at the rising clock edge.(after test_expr has reached the min limit value, the expression does not subsequently fall below the min limit or reach the max limit value.)

Status: simulation should pass

Author: pktiwari@noida.interrasystems.com

Date: 02-17-2006 

*************************************************************************************************************/

import OVLAssertions::*;

typedef enum {First_State, Second_State, Third_State, Fourth_State, Fifth_State} FSM_State deriving (Eq, Bits);

(* synthesize *)
module assertNoUnderflow1 (Empty);

Reg#(FSM_State) state <- mkRegA(First_State);

Reg#(Bit#(3)) test_expr <- mkRegA(3'b100);

let defaults = mkOVLDefaults;
defaults.min = 3; //min : 3
defaults.max = 5; //max : 5
AssertTest_IFC#(Bit#(3)) assertNoUnder <- bsv_assert_no_underflow(defaults);
   
rule test(True);
    assertNoUnder.test(test_expr);//test_expr : test_expr 
endrule

rule every (True);
    case (state)
    First_State:
	begin
	    state <= Second_State;
		test_expr <= 3'b011;
	end
	Second_State:
	begin
	    state <= Third_State;
		test_expr <= 3'b100;
	end
	Third_State:
	begin
	    state <= Fourth_State;
		test_expr <= 3'b101;		
	end
	Fourth_State:
	begin
	    state <= Fifth_State;
		test_expr <= 3'b100;
	end
	Fifth_State:
	begin
	    state <= First_State;
	    $finish(0);
	end
    endcase
endrule
endmodule
