/*************************************************************************************************************
Assertion-Checker: assert_always

Description: test_expr is TRUE at every rising clock-edge.

Status: simulation should pass

Author: pktiwari@noida.interrasystems.com

Date: 02-16-2006 

*************************************************************************************************************/

import OVLAssertions::*;

typedef enum {First_State, Second_State, Third_State, Fourth_State, Fifth_State} FSM_State deriving(Eq, Bits);

(* synthesize *)
module assertAlways1 (Empty);

Reg#(FSM_State) state <- mkRegA(First_State);
Reg#(Bool) test_expr <- mkRegA(True);

let defaults = mkOVLDefaults;
AssertTest_IFC#(Bool) assertAlw <- bsv_assert_always(defaults);
   
rule test;
    assertAlw.test(test_expr);//test_expr : test_expr
endrule

rule every (True);
    case (state)
    First_State:
	begin
	    state <= Second_State;
		test_expr <= True;
	end
	Second_State:
	begin
	    state <= Third_State;
	end
	Third_State:
	begin
	    state <= Fourth_State;
		test_expr <= True;
	end
	Fourth_State:
	begin
	    state <= Fifth_State;
	end
	Fifth_State:
	begin
	    state <= First_State;
		test_expr <= True;
	    $finish(0);
	end
    endcase
endrule
endmodule
