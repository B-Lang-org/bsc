/*----------------------------------------------------------------------------

Testbench for Example5Q

The expected output is:

Testing Ls:
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

import Example8Q::*;

typedef union tagged {
   void    Start;
   Bit#(3) Ignore1; // ignore the initial outputs
   Bit#(4) Ls;
   void    Done;	      
} State deriving (Eq, Bits);

module mkTb8 (Empty);

   // DUTs

   SShifter#(4,16) ls();
   mkLs the_ls(ls);

   // Testbench state
   
   Reg#(State) send_state();
   mkReg#(Start) send_state_r(send_state);

   Reg#(State) recv_state();
   mkReg#(Start) recv_state_r(recv_state);

   rule test;
      SXpair#(4,16) ls_push_val = ?;
      
      case (send_state) matches

	 tagged Start :
	    begin
	       send_state <= Ls(0);
	    end

	 tagged Ls .s :
	    begin
	       ls_push_val = tuple2(s, 16'hFFFF);
	       if (s == 15)
		  send_state <= Done;
	       else
		  send_state <= Ls(s+1);
	    end

	 default : noAction;

      endcase

      let ls_ret_val <- ls.push(ls_push_val);

      case (recv_state) matches

	 tagged Start :
	    begin
	       $display("Testing Ls:");
	       recv_state <= Ignore1(4);
	    end

	 tagged Ignore1 .n :
	    begin
	       if (n == 0)
		  recv_state <= Ls(0);
	       else
		  recv_state <= Ignore1(n-1);
	    end

	 tagged Ls .s :
	    begin
	       $display("16'hFFFF << 4'b%b = 16'b%b", s, ls_ret_val);
	       if (s == 15) begin
		  $display("Done");
		  $finish(0);
	       end
	       else
		  recv_state <= Ls(s+1);
	    end

      endcase
      
   endrule

endmodule

