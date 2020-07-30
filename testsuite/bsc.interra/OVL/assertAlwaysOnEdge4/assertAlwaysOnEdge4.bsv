/*************************************************************************************************************
Assertion-Checker: assert_always_on_edge (sampling_event tranistion edge_type: OVL_NEGEDGE)

Description: test_expr is not TRUE at every rising clock-edge after the sampling event encounters NEGEDGE transition.

Status: simulation should fail

Author: pktiwari@noida.interrasystems.com

Date: 02-16-2006 

*************************************************************************************************************/

import OVLAssertions::*;

typedef enum {First_State, Second_State, Third_State, Fourth_State, Fifth_State} FSM_State deriving(Eq, Bits);

(* synthesize *)
module assertAlwaysOnEdge4 (Empty);

Reg#(FSM_State) state <- mkRegA(First_State);
Reg#(Bool) test_expr <- mkRegA(False);
Reg#(Bool) sample <- mkRegA(True);

let defaults = mkOVLDefaults();
defaults.edge_type = OVL_NEGEDGE;

AssertSampleTest_IFC#(Bool) assertAlwOn <- bsv_assert_always_on_edge(defaults);
   
rule test;
    assertAlwOn.test(test_expr);//test_expr : test_expr
	assertAlwOn.sample(sample); //sampling_event : sample
endrule

rule every (True);
    case (state)
    First_State:
	begin
	    state <= Second_State;
		sample <= False;
	end
	Second_State:
	begin
	    state <= Third_State;
	end
	Third_State:
	begin
	    state <= Fourth_State;
		test_expr <= True;
	end
	Fourth_State:
	begin
	    state <= Fifth_State;
	end
	Fifth_State:
	begin
	    state <= First_State;
		test_expr <= True;
	    $finish(0);
	end
    endcase
endrule
endmodule
