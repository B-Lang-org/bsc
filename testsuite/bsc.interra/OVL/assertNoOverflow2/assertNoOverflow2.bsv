/*************************************************************************************************************
Assertion-Checker: assert_no_overflow

Description: test_expr overflows at a rising clock edge.(after test_expr has reached the max limit value, the expression subsequently exceeds the max limit value.)

Status: simulation should fail

Author: pktiwari@noida.interrasystems.com

Date: 02-17-2006 

*************************************************************************************************************/

import OVLAssertions::*;

typedef enum {First_State, Second_State, Third_State, Fourth_State, Fifth_State} FSM_State deriving (Eq, Bits);

(* synthesize *)
module assertNoOverflow2 (Empty);

Reg#(FSM_State) state <- mkRegA(First_State);

Reg#(Bit#(3)) test_expr <- mkRegA(0);

let defaults = mkOVLDefaults;
defaults.min = 0; //min : 0
defaults.max = 5; //max : 5
AssertTest_IFC#(Bit#(3)) assertNoOver <- bsv_assert_no_overflow(defaults);
   
rule test(True);
    assertNoOver.test(test_expr);//test_expr : test_expr 
endrule

rule every (True);
    case (state)
    First_State:
	begin
	    state <= Second_State;
		test_expr <= 3'b001;
	end
	Second_State:
	begin
	    state <= Third_State;
		test_expr <= 3'b101;
	end
	Third_State:
	begin
	    state <= Fourth_State;
		test_expr <= 3'b111;		
	end
	Fourth_State:
	begin
	    state <= Fifth_State;
		test_expr <= 3'b001;
	end
	Fifth_State:
	begin
	    state <= First_State;
	    $finish(0);
	end
    endcase
endrule
endmodule
