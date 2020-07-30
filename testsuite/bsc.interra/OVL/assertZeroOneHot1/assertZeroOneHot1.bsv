/*************************************************************************************************************
Assertion-Checker: assert_zero_one_hot

Description: test_expr is either 0 or it has only bit set to "1" at every rising clock edge.

Status: simulation should pass

Author: pktiwari@noida.interrasystems.com

Date: 02-17-2006 

*************************************************************************************************************/

import OVLAssertions::*;

typedef enum {First_State, Second_State, Third_State, Fourth_State, Fifth_State} FSM_State deriving(Eq, Bits);

(* synthesize *)
module assertZeroOneHot1 (Empty);

Reg#(FSM_State) state <- mkRegA(First_State);

Reg#(Bit#(3)) test_expr <- mkRegA(3'b001);

let defaults = mkOVLDefaults;
AssertTest_IFC#(Bit#(3)) assertZeroOneH <- bsv_assert_zero_one_hot(defaults);
   
rule test(True);
    assertZeroOneH.test(test_expr); // test_expr : test_expr
endrule

rule every (True);
    case (state)
    First_State:
	begin
	    state <= Second_State;
		test_expr <= 3'b010;
	end
	Second_State:
	begin
	    state <= Third_State;
		test_expr <= 3'b100;
	end
	Third_State:
	begin
	    state <= Fourth_State;
		test_expr <= 3'b001;
	end
	Fourth_State:
	begin
	    state <= Fifth_State;
		test_expr <= 3'b000;
	end
	Fifth_State:
	begin
	    state <= First_State;
	    $finish(0);
	end
    endcase
endrule
endmodule
