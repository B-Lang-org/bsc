/*************************************************************************************************************
Assertion-Checker: assert_width

Description: test_expr goes HIGH and remains HIGH for more than max_cks no. of clock cycles.

Status: simulation should fail

Author: pktiwari@noida.interrasystems.com

Date: 02-17-2006 

*************************************************************************************************************/

import OVLAssertions::*;

typedef enum {First_State, Second_State, Third_State, Fourth_State, Fifth_State, Sixth_State, Seventh_State} FSM_State deriving (Eq, Bits);

(* synthesize *)
module assertWidth3 (Empty);

Reg#(FSM_State) state <- mkRegA(First_State);

Reg#(Bool) test_expr <- mkRegA(False);

let defaults = mkOVLDefaults;
defaults.min_cks = 2; //min_cks : 2
defaults.max_cks = 3; //max_cks : 3
AssertTest_IFC#(Bool) assertWid <- bsv_assert_width(defaults);
      
rule test(True);
    assertWid.test(test_expr); //test_expr : test_expr
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
	end
	Fourth_State:
	begin
	    state <= Fifth_State;
	end
	Fifth_State:
	begin
	    state <= Sixth_State;
	    test_expr <= False;
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
