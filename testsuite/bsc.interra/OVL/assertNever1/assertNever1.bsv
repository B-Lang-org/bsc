/*************************************************************************************************************
Assertion-Checker: assert_never

Description: test_expr is not TRUE at every rising clock-edge.

Status: simulation should pass

Author: pktiwari@noida.interrasystems.com

Date: 02-17-2006 

*************************************************************************************************************/

import OVLAssertions::*;

typedef enum {First_State, Second_State, Third_State, Fourth_State, Fifth_State} FSM_State deriving(Eq, Bits);

(* synthesize *)
module assertNever1 (Empty);

Reg#(FSM_State) state <- mkRegA(First_State);
Reg#(Bool) test_expr <- mkRegA(False);

let defaults = mkOVLDefaults;
AssertTest_IFC#(Bool) assertNev <- bsv_assert_never(defaults);
   
rule test;
    assertNev.test(test_expr); //test_expr : test_expr
endrule

rule every (True);
    case (state)
    First_State:
	begin
	    state <= Second_State;
		test_expr <= False;
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
	end
	Fifth_State:
	begin
	    state <= First_State;
	    $finish(0);
	end
    endcase
endrule
endmodule
