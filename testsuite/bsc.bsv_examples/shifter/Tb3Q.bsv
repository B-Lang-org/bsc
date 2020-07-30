/*----------------------------------------------------------------------------

Testbench for Example3Q

The expected output is:

Testing f:
16'hFFFF << 4'b0000 = 16'b1111111111111111
16'hFFFF << 4'b0001 = 16'b1111111111111110
16'hFFFF << 4'b0010 = 16'b1111111111111100
16'hFFFF << 4'b0011 = 16'b1111111111111000
16'hFFFF << 4'b0100 = 16'b1111111111110000
16'hFFFF << 4'b0101 = 16'b1111111111100000
16'hFFFF << 4'b0110 = 16'b1111111111000000
16'hFFFF << 4'b0111 = 16'b1111111110000000
16'hFFFF << 4'b1000 = 16'b1111111100000000
16'hFFFF << 4'b1001 = 16'b1111111000000000
16'hFFFF << 4'b1010 = 16'b1111110000000000
16'hFFFF << 4'b1011 = 16'b1111100000000000
16'hFFFF << 4'b1100 = 16'b1111000000000000
16'hFFFF << 4'b1101 = 16'b1110000000000000
16'hFFFF << 4'b1110 = 16'b1100000000000000
16'hFFFF << 4'b1111 = 16'b1000000000000000
Done
 
-----------------------------------------------------------------------------*/

import Example3Q::*;

typedef union tagged {
   void    Start;
   Bit#(4) Test;
} State deriving (Eq, Bits);

module mkTb3 (Empty);

   Reg#(State) state();
   mkReg#(Start) state_r(state);
   
   rule test;
      case (state) matches

	 tagged Start : begin
	    $display("Testing f:");
	    state <= Test(0);
	 end
	 
	 tagged Test .s : begin
	    $display("16'hFFFF << 4'b%b = 16'b%b", s, f(s, 16'hFFFF));
	    if (s == 15) begin
	       $display("Done");
	       $finish(0);
	    end
	    else
	       state <= Test(s+1);
	 end

      endcase
   endrule
   
endmodule

