/*************************************************************************************************************
Assertion-Checker: assert_win_unchange

Description: test_expr changes value between the start_event and stop_event.

Status: simulation should fail

Author: pktiwari@noida.interrasystems.com

Date: 02-17-2006 

*************************************************************************************************************/

import OVLAssertions ::*;

typedef enum {First_State, Second_State, Third_State, Fourth_State, Fifth_State} FSM_State deriving (Eq, Bits);

(* synthesize *)
module assertWinUnchange2 (Empty);

Reg#(FSM_State) state <- mkRegA(First_State);
   
Reg#(Bit#(3)) test_expr <- mkRegA(0);

let defaults = mkOVLDefaults;
AssertStartStopTest_IFC#(Bit#(3)) assertWinUnch <- bsv_assert_win_unchange(defaults);
   
rule test(True);
    assertWinUnch.start(state == Second_State);//start_event : Second_State
	assertWinUnch.stop(state == Fourth_State); //end_event : Fourth_State
    assertWinUnch.test(test_expr);             //test_expr : test_expr
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
	end
	Third_State:
	begin
	    state <= Fourth_State;
		test_expr <= 3'b010;		
	end
	Fourth_State:
	begin
	    state <= Fifth_State;
	end
	Fifth_State:
	begin
	    state <= First_State;
		test_expr <= 3'b011;		
	    $finish(0);
	end
    endcase
endrule
endmodule
