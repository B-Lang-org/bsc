/*************************************************************************************************************
Assertion-Checker: assert_decrement

Description: test_expr decrements by the given value at the rising clock-edge.

Status: simulation should pass

Author: pktiwari@noida.interrasystems.com

Date: 02-17-2006 

*************************************************************************************************************/

import OVLAssertions::*;

typedef enum {First_State, Second_State, Third_State, Fourth_State, Fifth_State} FSM_State deriving(Eq, Bits);

(* synthesize *)
module assertDecrement1 (Empty);

Reg#(FSM_State) state <- mkRegA(First_State);
Reg#(Bit#(3)) test_expr <- mkRegA(3'b110);

let defaults = mkOVLDefaults;
defaults.value = 2; //decrement value : 2

AssertTest_IFC#(Bit#(3)) assertDec <- bsv_assert_decrement(defaults);
   
rule test(True);
    assertDec.test(test_expr); // test_expr : test_expr
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
	end
	Fourth_State:
	begin
	    state <= Fifth_State;
	end
	Fifth_State:
	begin
	    state <= First_State;
	    $finish(0);
	end
    endcase
endrule
endmodule
