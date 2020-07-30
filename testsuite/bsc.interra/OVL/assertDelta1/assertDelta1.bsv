/*************************************************************************************************************
Assertion-Checker: assert_delta

Description: test_expr changes by a value in the specified range at the rising clock edge.

Status: simulation should pass

Author: pktiwari@noida.interrasystems.com

Date: 02-17-2006 

*************************************************************************************************************/

import OVLAssertions::*;

typedef enum {First_State, Second_State, Third_State, Fourth_State, Fifth_State} FSM_State deriving(Eq, Bits);

(* synthesize *)
module assertDelta1 (Empty);

Reg#(FSM_State) state <- mkRegA(First_State);
Reg#(Bit#(3)) test_expr <- mkRegA(0);

let defaults = mkOVLDefaults;
defaults.min = 2; //min : 2
defaults.max = 4; //max : 4

AssertTest_IFC#(Bit#(3)) assertDel <- bsv_assert_delta(defaults);
                                                              
   
rule test(True);
    assertDel.test(test_expr); // test_expr : test_expr
endrule

rule every (True);
    case (state)
    First_State:
	begin
	    state <= Second_State;
		test_expr  <= 3'b010;
	end
	Second_State:
	begin
	    state <= Third_State;
		test_expr  <= 3'b100;
	end
	Third_State:
	begin
	    state <= Fourth_State;
		test_expr <= 3'b111;
	end
	Fourth_State:
	begin
	    state <= Fifth_State;
		test_expr <= 3'b101;
	end
	Fifth_State:
	begin
	    state <= First_State;
	    $finish(0);
	end
    endcase
endrule
endmodule
