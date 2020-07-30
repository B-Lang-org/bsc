/*************************************************************************************************************
Assertion-Checker: assert_never_unknown_async

Description: test expression doesn't contain only 0 and 1 bits. 

Status: simulation should fail

Author: pktiwari@noida.interrasystems.com

Date: 03-06-2006 

*************************************************************************************************************/

import OVLAssertions::*;
import ZBusUtil ::*;

typedef enum {First_State, Second_State, Third_State, Fourth_State, Fifth_State} FSM_State deriving (Eq, Bits);

(* synthesize *)
module assertNeverUnknownAsync2 (Empty);

Reg#(FSM_State) state <- mkRegA(First_State);
Reg#(Bit#(3)) test_expr <- mkRegA(0);
ConvertToZ#(Bit#(3)) z_value <- mkConvertToZ;

let defaults = mkOVLDefaults;

AssertTest_IFC#(Bit#(3)) assertNevUnknownAsyn <- bsv_assert_never_unknown_async(defaults);   

rule test(True);
	assertNevUnknownAsyn.test(test_expr); //test_expr : test_expr
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
		test_expr  <= 3'b010;
	 end
	 Third_State:
	 begin
	    state <= Fourth_State;
		test_expr  <= pack(z_value.convert(0, False));
	 end
	 Fourth_State:
	 begin
	    state <= Fifth_State;
	 end
	 Fifth_State:
	 begin
	    state <= First_State;
		test_expr  <= 3'b000;
	    $finish(0);
	 end
     endcase
endrule
endmodule
