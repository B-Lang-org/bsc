package Divider;

import GetPut::*;
import RegFile::*;

interface Divider;
	method Action dividerInputs (Tuple2#(Bit#(12), Bit#(7)) inp);
	method Tuple2#(Bit#(9), Bit#(9)) dividerOutputs();
endinterface: Divider

typedef enum {Initialize, Compute, Idle} States deriving(Eq, Bits);

(* synthesize *)
module mkDivider(Divider);
	Reg#(Bit#(12)) dividend <- mkReg(0);
	Reg#(Bit#(7)) divisor <- mkReg(0);
	Reg#(Bit#(9)) difference <- mkReg(0);
	Reg#(Bit#(9)) quotient <- mkReg(0);
	Reg#(Bit#(9)) remainder <- mkReg(0);
	
	Reg#(Bool) ready <- mkReg(True);
	Reg#(States) state <- mkReg(Idle);
	Reg#(Bit#(5)) stateCount <- mkReg(0);

	RegFile#(Bit#(5), Bit#(18)) lookupTable <- mkRegFile (0, 21);

	Bit#(9) tempRem = 0, tempQuot = 0;
	
	function 
	Tuple2#(Bit#(9), Bit#(9)) 
	subtractDifference (Bit#(9) quotient, Bit#(9) remainder, 
					  RegFile#(Bit#(5), Bit#(18)) lookupTable);
		Bit#(18) tempLookupValue;
		Bit#(9) differenceQuotient;
		Bit#(9) differenceRemainder;

		// Lookup difference
		tempLookupValue = lookupTable.sub(truncate(quotient));	
		differenceQuotient = tempLookupValue[17:9];
		differenceRemainder = tempLookupValue[8:0];
		// Apply difference to quotient and remainder
		quotient = quotient - differenceQuotient;
		if (remainder < differenceRemainder)
		begin
			remainder = remainder + zeroExtend(divisor) 
								   - differenceRemainder;
			quotient = quotient - 1;
		end
		else
			remainder = remainder - differenceRemainder;

		return tuple2(quotient, remainder);
	endfunction: subtractDifference	
	
	function 
	Tuple2#(Bit#(9), Bit#(9)) 
	addDifference (Bit#(9) quotient, Bit#(9) remainder,
				  RegFile#(Bit#(5), Bit#(18)) lookupTable);
		Bit#(18) tempLookupValue;
		Bit#(9) differenceQuotient;
		Bit#(9) differenceRemainder;

		// Lookup difference
		tempLookupValue = lookupTable.sub(truncate(quotient));	
		differenceQuotient = tempLookupValue[17:9];
		differenceRemainder = tempLookupValue[8:0];

		//Apply the difference
		quotient = quotient + differenceQuotient;
		remainder = remainder + differenceRemainder;
		if (remainder > zeroExtend(divisor))
		begin
			remainder = remainder - zeroExtend(divisor);
			quotient = quotient + 1;
		end
		return tuple2(quotient, remainder);
	endfunction: addDifference

	for (Integer i = 0; i < 22; i = i+1)
	begin
		rule initializationRule(state == Initialize && 
								stateCount == fromInteger(i));
			lookupTable.upd (fromInteger(i), {tempQuot, tempRem});
			if (stateCount == 21)
			begin
				ready <= True;
				stateCount <= 0;
				state <= Compute;
			end
			else 
			stateCount <= stateCount + 1;
		endrule

		tempRem = tempRem + difference;
		if (tempRem > zeroExtend(divisor)-1)
		begin
			tempRem = tempRem - zeroExtend(divisor);
			tempQuot = tempQuot + 1;
		end
	end

	// Step1: For each of the "expected" divisors determine the closest
	// power of two and then determine the quotient and remainder w.r.t 
	// that power of 2. 
	// Step2: Perform lookup on table to determine the difference 
	// quotient and remainders
	// Step3: Compute the Difference over the quotient and remainder 
	// computed with the closest power of two.
	rule compute (state == Compute);
		Bit#(9) tempQuotient;
		Bit#(9) tempRemainder;
		Tuple2#(Bit#(9), Bit#(9)) tempTuple;

		case (divisor)
			6:
				begin
					// The quotient and remainder for the closest power of 2
					// i.e. 8
					tempQuotient = dividend[11:3];
					tempRemainder = zeroExtend(dividend[2:0]);
					tempTuple = addDifference (tempQuotient, tempRemainder, lookupTable);
					quotient <= tpl_1(tempTuple);
					remainder <= tpl_2(tempTuple);
				end
			8: 
				begin
					quotient <= dividend[11:3];
					remainder <= zeroExtend(dividend[2:0]);
				end
			9,
			11: 
				begin
					// The quotient and remainder for the closest power of 2
					// i.e. 8
					tempQuotient = dividend[11:3];
					tempRemainder = zeroExtend(dividend[2:0]);
					tempTuple = subtractDifference (tempQuotient, tempRemainder, lookupTable);
					quotient <= tpl_1(tempTuple);
					remainder <= tpl_2(tempTuple);
				end
			15:
				begin
					// The quotient and remainder for the closest power of 2
					// i.e. 16
					tempQuotient = zeroExtend(dividend[11:4]);
					tempRemainder = zeroExtend(dividend[3:0]);
					tempTuple = addDifference (tempQuotient, tempRemainder, lookupTable);
					quotient <= tpl_1(tempTuple);
					remainder <= tpl_2(tempTuple);
				end
			18,
			20,
			22:
				begin
					// The quotient and remainder for the closest power of 2
					// i.e. 16
					tempQuotient = zeroExtend(dividend[11:4]);
					tempRemainder = zeroExtend(dividend[3:0]);
					tempTuple = subtractDifference (tempQuotient, tempRemainder, lookupTable);
					quotient <= tpl_1(tempTuple);
					remainder <= tpl_2(tempTuple);
				end
			30:
				begin
					// The quotient and remainder for the closest power of 2
					// i.e. 32
					tempQuotient = zeroExtend(dividend[11:5]);
					tempRemainder = zeroExtend(dividend[4:0]);
					tempTuple = addDifference (tempQuotient, tempRemainder, lookupTable);
					quotient <= tpl_1(tempTuple);
					remainder <= tpl_2(tempTuple);
				end
			36,
			40,
			44,
			45:
				begin
					// The quotient and remainder for the closest power of 2
					// i.e. 32
					tempQuotient = zeroExtend(dividend[11:5]);
					tempRemainder = zeroExtend(dividend[4:0]);
					tempTuple = subtractDifference (tempQuotient, tempRemainder, lookupTable);
					quotient <= tpl_1(tempTuple);
					remainder <= tpl_2(tempTuple);
				end
			50:
				begin
					// The quotient and remainder for the closest power of 2
					// i.e. 64
					tempQuotient = zeroExtend(dividend[11:6]);
					tempRemainder = zeroExtend(dividend[5:0]);
					tempTuple = addDifference (tempQuotient, tempRemainder, lookupTable);
					quotient <= tpl_1(tempTuple);
					remainder <= tpl_2(tempTuple);
				end
			64:
				begin
					quotient <= zeroExtend(dividend[11:6]);
					remainder <= zeroExtend(dividend[5:0]);
				end
			80:
				begin
					// The quotient and remainder for the closest power of 2
					// i.e. 64
					tempQuotient = zeroExtend(dividend[11:6]);
					tempRemainder = zeroExtend(dividend[5:0]);
					tempTuple = subtractDifference (tempQuotient, tempRemainder, lookupTable);
					quotient <= tpl_1(tempTuple);
					remainder <= tpl_2(tempTuple);
				end
		endcase
		ready <= True;
		state <= Idle;
	endrule: compute 	

	method Action dividerInputs(inp) if (ready == True);
		dividend <= tpl_1(inp);
		if (divisor != tpl_2(inp))
		begin
			case (tpl_2(inp))
				6: 
					begin
						difference <= 2;
						state <= Initialize;
					end
				9: 
					begin
						difference <= 1;
						state <= Initialize;
					end
				11: 
					begin
						difference <= 3;
						state <= Initialize;
					end
				15: 
					begin
						difference <= 1;
						state <= Initialize;
					end
				18: 
					begin
						difference <= 2;
						state <= Initialize;
					end
				20: 
					begin
						difference <= 4;
						state <= Initialize;
					end
				22: 
					begin
						difference <= 6;
						state <= Initialize;
					end
				30: 
					begin
						difference <= 2;
						state <= Initialize;
					end
				40:
					begin
						difference <= 8;
						state <= Initialize;
					end
				44:
					begin
						difference <= 12;
						state <= Initialize;
					end
				50:
					begin
						difference <= 14;
						state <= Initialize;
					end
				80: 
					begin
						difference <= 16;
						state <= Initialize;
					end
				default:
					state<= Compute;
			endcase
			divisor <= tpl_2(inp);
		end
		else
			state <= Compute;
		ready <= False;
	endmethod: dividerInputs

	method Tuple2#(Bit#(9), Bit#(9)) dividerOutputs if (ready == True);
		return tuple2(quotient, remainder);
	endmethod: dividerOutputs
endmodule: mkDivider

endpackage: Divider
