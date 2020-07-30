/*************************************************************************************************************
Assertion-Checker: assert_fifo_index

Description: a FIFO-type structure underflows. 

Status: simulation should fail

Author: pktiwari@noida.interrasystems.com

Date: 03-10-2006 

*************************************************************************************************************/
import OVLAssertions ::*;

typedef enum {First_State, Second_State, Third_State, Fourth_State, Fifth_State, Sixth_State, Seventh_State} FSM_State deriving(Eq, Bits);

(* synthesize *)
module assertFifoIndex3(Empty);

Reg#(FSM_State) state <- mkRegA(First_State);
Reg#(Bit#(1)) push <- mkRegA(0);
Reg#(Bit#(1)) pop  <- mkRegA(0);

let defaults = mkOVLDefaults;
defaults.depth = 2;
AssertFifoTest_IFC#(Bit#(1), Bit#(1)) assertFifoI <- bsv_assert_fifo_index(defaults);
      
rule test(True);
    assertFifoI.push(push); 
    assertFifoI.pop(pop);
endrule

rule every (True);
    case (state)
    First_State:
	begin
	    state <= Second_State;
		pop <= 1;
	end
	Second_State:
	begin
	    state <= Third_State;
		push <= 1;
		pop <= 1;
	end
	Third_State:
	begin
	    state <= Fourth_State;
		pop <= 1;
	end
	Fourth_State:
	begin
	    state <= Fifth_State;
		pop <= 1;
	end
	Fifth_State:
	begin
	    state <= Sixth_State;
		pop <= 1;
	end
	Sixth_State:
	begin
	    state <= Seventh_State;
		pop <= 1;
	end
	Seventh_State:
	begin
	    state <= First_State;
	    $finish(0);
	end
    endcase
endrule
endmodule
