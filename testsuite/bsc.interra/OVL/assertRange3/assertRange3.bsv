/*************************************************************************************************************
Assertion-Checker: assert_range

Description: test_expr is more than the max value at the rising clock edge.

Status: simulation should fail

Author: pktiwari@noida.interrasystems.com

Date: 02-17-2006 

*************************************************************************************************************/

import OVLAssertions::*;

typedef enum {First_State, Second_State, Third_State, Fourth_State, Fifth_State, Sixth_State, Seventh_State} FSM_State deriving(Eq, Bits);

(* synthesize *)

module assertRange3 (Empty);

Reg#(FSM_State) state <- mkRegA(First_State);
Reg#(Bit#(4)) test_expr  <- mkRegA(4'b0100);

let defaults = mkOVLDefaults;
defaults.min = 4; //min : 4
defaults.max = 8; //max : 8
AssertTest_IFC#(Bit#(4)) assertRan <- bsv_assert_range(defaults);
      
rule test(True);
   assertRan.test(test_expr); // test_expr : test_expr
endrule

rule every (True);
    case (state)
    First_State:
	begin
	    state <= Second_State;
		test_expr <= 4'b0011;
	end
	Second_State:
	begin
	    state <= Third_State;
		test_expr <= 4'b1010;
	end
	Third_State:
	begin
	    state <= Fourth_State;
		test_expr <= 4'b1100;
	end
	Fourth_State:
	begin
	    state <= Fifth_State;
		test_expr  <= 4'b1000;
	end
	Fifth_State:
	begin
	    state <= Sixth_State;
		test_expr <= 4'b0010;
	end
	Sixth_State:
	begin
	    state <= Seventh_State;
	end
	Seventh_State:
	begin
	    state <= First_State;
	    $finish(0);
	end
    endcase
endrule
endmodule
