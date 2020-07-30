/*************************************************************************************************************
Assertion-Checker: assert_handshake

Description: Multiple requests are not made while waiting for an acknowledgement and that every ack is in response to a unique req.

Status: simulation should pass

Author: pktiwari@noida.interrasystems.com

Date: 02-17-2006 

*************************************************************************************************************/

import OVLAssertions ::*;

typedef enum {First_State, Second_State, Third_State, Fourth_State, Fifth_State, Sixth_State, Seventh_State} FSM_State deriving(Eq, Bits);

(* synthesize *)
module assertHandshake1 (Empty);

Reg#(FSM_State) state <- mkRegA(First_State);
Reg#(Bool) req <- mkRegA(False);
Reg#(Bool) ack <- mkRegA(False);

let defaults = mkOVLDefaults;
defaults.min_ack_cycle = 1;//min_ack_cycle : 1
defaults.max_ack_cycle = 3;//max_ack_cycle : 3
AssertStartTest_IFC#(Bool) assertHand <- bsv_assert_handshake(defaults);
      
rule test(True);
    assertHand.start(req); // req : req
    assertHand.test(ack); //  ack : ack
endrule

rule every (True);
    case (state)
    First_State:
	begin
	    state <= Second_State;
		req <= True;
	end
	Second_State:
	begin
	    state <= Third_State;
		ack <= True;
		req <= False;
	end
	Third_State:
	begin
	    state <= Fourth_State;
		ack <= False;
	end
	Fourth_State:
	begin
	    state <= Fifth_State;
		req  <= True;
	end
	Fifth_State:
	begin
	    state <= Sixth_State;
		ack  <= True;
	end
	Sixth_State:
	begin
	    state <= Seventh_State;
		req <= False;
		ack <= False;
	end
	Seventh_State:
	begin
	    state <= First_State;
	    $finish(0);
	end
    endcase
endrule
endmodule
