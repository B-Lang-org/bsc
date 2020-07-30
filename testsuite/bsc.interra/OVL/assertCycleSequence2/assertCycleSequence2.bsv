/*************************************************************************************************************
Assertion-Checker: assert_cycle_sequence

Description: a specified necessary condition occurs and it is not followed by a specified sequence of events. 

Status: simulation should pass

Author: pktiwari@noida.interrasystems.com

Date: 03-06-2006 

*************************************************************************************************************/

import OVLAssertions::*;

typedef enum {First_State, Second_State, Third_State, Fourth_State, Fifth_State} FSM_State deriving (Eq, Bits);

(* synthesize *)
module assertCycleSequence2 (Empty);

   Reg#(FSM_State) state <- mkRegA(First_State);
   Reg#(Bit#(3)) test_expr <- mkRegA(0);

   let defaults = mkOVLDefaults;

   AssertTest_IFC#(Bit#(3)) assertCycle <- bsv_assert_cycle_sequence(defaults);   

   rule test(True);
      assertCycle.test(test_expr); //event_sequence : test_expr
   endrule

   rule every (True);
      case (state)
	 First_State:
	 begin
	    state <= Second_State;
	    test_expr  <= 3'b100;
	 end
	 Second_State:
	 begin
	    state <= Third_State;
	    test_expr  <= 3'b010;
	 end
	 Third_State:
	 begin
	    state <= Fourth_State;
	    test_expr  <= 3'b010;
	 end
	 Fourth_State:
	 begin
	    state <= Fifth_State;
	    test_expr <= 3'b100;
	 end
	 Fifth_State:
	 begin
	    state <= First_State;
	    test_expr  <= 3'b110;
	    $finish(0);
	 end
      endcase
   endrule
endmodule
