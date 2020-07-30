/*************************************************************************************************************
Assertion-Checker: assert_window

Description: test_expr holds TRUE in a window specified by start_event and end_event.

Status: simulation should pass

Author: pktiwari@noida.interrasystems.com

Date: 02-17-2006 

*************************************************************************************************************/

import OVLAssertions ::*;

typedef enum {First_State, Second_State, Third_State, Fourth_State, Fifth_State, Sixth_State, Seventh_State} FSM_State deriving(Eq, Bits);

(* synthesize *)
module assertWindow1 (Empty);

Reg#(FSM_State) state <- mkRegA(First_State);
Reg#(Bool) test_expr <- mkRegA(False);

let defaults = mkOVLDefaults;
AssertStartStopTest_IFC#(Bool) assertWin <- bsv_assert_window(defaults);
      
rule test(True);
    assertWin.test(test_expr);//test_expr : test_expr
    assertWin.start(state == Second_State); // start_event : Second_State
    assertWin.stop(state == Fifth_State);   // end_event : Fifth_State
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
		test_expr  <= True;
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
		test_expr  <= False;
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
