/*************************************************************************************************************
Assertion-Checker: assert_unchange

Description: test_expr remains unchaged for num_cks clock cycles after the start_event is asserted.

Status: simulation should pass

Author: pktiwari@noida.interrasystems.com

Date: 02-17-2006 

*************************************************************************************************************/

import OVLAssertions ::*;

typedef enum {First_State, Second_State, Third_State, Fourth_State, Fifth_State} FSM_State deriving (Eq, Bits);

(* synthesize *)
module assertUnchange1 (Empty);

Reg#(FSM_State) state <- mkRegA(First_State);
   
Reg#(Bit#(3)) test_expr <- mkRegA(0);

let defaults = mkOVLDefaults;
defaults.num_cks = 3; //num_cks : 3
AssertStartTest_IFC#(Bit#(3)) assertUnch <- bsv_assert_unchange(defaults);
   
rule test(True);
    assertUnch.start(state == Second_State);//start_event : Second_State
    assertUnch.test(test_expr);             //test_expr : test_expr
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
	end
	Fourth_State:
	begin
	    state <= Fifth_State;
		test_expr <= 3'b010;		
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
