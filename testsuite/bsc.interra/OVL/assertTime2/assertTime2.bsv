/*************************************************************************************************************
Assertion-Checker: assert_time

Description: test_expr remains TRUE for less than num_cks no .of clock cycles after the start_event is asserted.

Status: simulation should fail

Author: pktiwari@noida.interrasystems.com

Date: 02-17-2006 

*************************************************************************************************************/

import OVLAssertions ::*;

typedef enum {First_State, Second_State, Third_State, Fourth_State, Fifth_State} FSM_State deriving (Eq, Bits);

(* synthesize *)
module assertTime2 (Empty);

Reg#(FSM_State) state <- mkRegA(First_State);
   
Reg#(Bool) test_expr <- mkRegA(False);

let defaults = mkOVLDefaults;
defaults.num_cks = 3; //num_cks : 3
AssertStartTest_IFC#(Bool) assertTim <- bsv_assert_time(defaults);
   
rule test(True);
    assertTim.start(state == Second_State);//start_event : Second_State
    assertTim.test(test_expr);             //test_expr : test_expr
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
		test_expr <= True;		
	end
	Third_State:
	begin
	    state <= Fourth_State;
		test_expr <= False;		
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
