/*************************************************************************************************************
Assertion-Checker: assert_implication

Description: antecedent_expr is TRUE and consequent_expr is also TRUE at the same clock edge.

Status: simulation should pass

Author: pktiwari@noida.interrasystems.com

Date: 02-17-2006 

*************************************************************************************************************/

import OVLAssertions::*;

typedef enum {First_State, Second_State, Third_State, Fourth_State, Fifth_State} FSM_State deriving (Eq, Bits);

(* synthesize *)
module assertImplication1 (Empty);

Reg#(FSM_State) state <- mkRegA(First_State);
Reg#(Bool) consq <- mkRegA(False);

let defaults = mkOVLDefaults;
AssertStartTest_IFC#(Bool) assertImp <- bsv_assert_implication(defaults);
   
rule test(True);
    assertImp.start(state == Third_State);//antecedent_expr : Third_State
    assertImp.test(consq);           //consequent_expr : consq
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
	    consq <= True; 
	end
	Third_State:
	begin
	    state <= Fourth_State;
	end
	Fourth_State:
	begin
	    state <= Fifth_State;
		consq <= False;
	end
	Fifth_State:
	begin
	    state <= First_State;
	    $finish(0);
	end
    endcase
endrule
endmodule
