/*************************************************************************************************************
Assertion-Checker: assert_one_cold

Description: test_expr has exactly one bit set to "0" at the rising clock edge.

Status: simulation should pass

Author: pktiwari@noida.interrasystems.com

Date: 02-17-2006 

*************************************************************************************************************/

import OVLAssertions::*;

typedef enum {First_State, Second_State, Third_State, Fourth_State, Fifth_State} FSM_State deriving(Eq, Bits);

(* synthesize *)
module assertOneCold1 (Empty);

Reg#(FSM_State) state <- mkRegA(First_State);

Reg#(Bit#(3)) test_expr <- mkRegA(3'b011);

let defaults = mkOVLDefaults;
AssertTest_IFC#(Bit#(3)) assertOneC <- bsv_assert_one_cold(defaults);
   
rule test(True);
    assertOneC.test(test_expr); // test_expr : test_expr
endrule

rule every (True);
    case (state)
    First_State:
	begin
	    state <= Second_State;
		test_expr <= 3'b110;
	end
	Second_State:
	begin
	    state <= Third_State;
		test_expr <= 3'b101;
	end
	Third_State:
	begin
	    state <= Fourth_State;
		test_expr <= 3'b110;
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
