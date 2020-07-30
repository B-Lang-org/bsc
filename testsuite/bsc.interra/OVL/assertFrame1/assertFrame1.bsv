/*************************************************************************************************************
Assertion-Checker: assert_frame

Description: After the start_event is asserted, the single bit test_expr goes HIGH not before the min_cks and not after the max_cks no. of clock cycles.

Status: simulation should pass

Author: pktiwari@noida.interrasystems.com

Date: 02-17-2006 

*************************************************************************************************************/

import OVLAssertions::*;

typedef enum {First_State, Second_State, Third_State, Fourth_State, Fifth_State, Sixth_State, Seventh_State} FSM_State deriving(Eq, Bits);

(* synthesize *)

module assertFrame1 (Empty);

Reg#(FSM_State) state <- mkRegA(First_State);
Reg#(Bool) test_expr  <- mkRegA(False);

let defaults = mkOVLDefaults;
defaults.min_cks = 2;//min_cks : 2
defaults.max_cks = 3;//max_cks : 3
AssertStartTest_IFC#(Bool) assertFr <- bsv_assert_frame(defaults);
      
rule test(True);
   assertFr.test(test_expr); // test_expr : test_expr
   assertFr.start(state == Second_State); //start_event : Second_State
endrule

rule every (True);
    case (state)
    First_State:
	begin
	    state <= Second_State;
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
		test_expr  <= True;
	end
	Fifth_State:
	begin
	    state <= Sixth_State;
	end
	Sixth_State:
	begin
	    state <= Seventh_State;
	 	test_expr <= False;
	end
	Seventh_State:
	begin
	    state <= First_State;
	    $finish(0);
	end
    endcase
endrule
endmodule
