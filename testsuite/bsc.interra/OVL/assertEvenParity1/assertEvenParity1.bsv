/*************************************************************************************************************
Assertion-Checker: assert_even_parity

Description: test_expr is 0 or it has even no. of bits set to "1" at every rising clock edge.

Status: simulation should pass

Author: pktiwari@noida.interrasystems.com

Date: 02-17-2006 

*************************************************************************************************************/

import OVLAssertions::*;

typedef enum {First_State, Second_State, Third_State, Fourth_State, Fifth_State} FSM_State deriving(Eq, Bits);

(* synthesize *)
module assertEvenParity1 (Empty);

Reg#(FSM_State) state <- mkRegA(First_State);

Reg#(Bit#(5)) test_expr <- mkRegA(0);

let defaults = mkOVLDefaults;
AssertTest_IFC#(Bit#(5)) assertEven <- bsv_assert_even_parity(defaults);
   
rule test(True);
    assertEven.test(test_expr); // test_expr : test_expr
endrule

rule every (True);
    case (state)
    First_State:
	begin
	    state <= Second_State;
		test_expr  <= 5'b01010;
	end
	Second_State:
	begin
	    state <= Third_State;
		test_expr  <= 5'b01100;
	end
	Third_State:
	begin
	    state <= Fourth_State;
		test_expr <= 5'b10111;
	end
	Fourth_State:
	begin
	    state <= Fifth_State;
		test_expr <= 5'b00101;
	end
	Fifth_State:
	begin
	    state <= First_State;
		test_expr <= 5'b0;
	    $finish(0);
	end
    endcase
endrule
endmodule
