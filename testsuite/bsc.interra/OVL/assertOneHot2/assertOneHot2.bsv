/*************************************************************************************************************
Assertion-Checker: assert_one_hot

Description: test_expr has more than one bits set to "1" at the rising clock edge.

Status: simulation should fail

Author: pktiwari@noida.interrasystems.com

Date: 02-17-2006 

*************************************************************************************************************/

import OVLAssertions::*;

typedef enum {First_State, Second_State, Third_State, Fourth_State, Fifth_State} FSM_State deriving(Eq, Bits);

(* synthesize *)
module assertOneHot2 (Empty);

Reg#(FSM_State) state <- mkRegA(First_State);

Reg#(Bit#(3)) test_expr <- mkRegA(3'b001);

let defaults = mkOVLDefaults;
AssertTest_IFC#(Bit#(3)) assertOneH <- bsv_assert_one_hot(defaults);
   
rule test(True);
    assertOneH.test(test_expr); // test_expr : test_expr
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
		test_expr <= 3'b011;
	end
	Third_State:
	begin
	    state <= Fourth_State;
		test_expr <= 3'b101;
	end
	Fourth_State:
	begin
	    state <= Fifth_State;
		test_expr <= 3'b110;
	end
	Fifth_State:
	begin
	    state <= First_State;
		test_expr <= 3'b001;
	    $finish(0);
	end
    endcase
endrule
endmodule
