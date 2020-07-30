/*----------------------------------------------------------------------------

Testbench for Example5Q

The expected output is:

Testing Ls3:
8'hFF << 3'b000 = 8'b11111111
8'hFF << 3'b001 = 8'b11111110
8'hFF << 3'b010 = 8'b11111100
8'hFF << 3'b011 = 8'b11111000
8'hFF << 3'b100 = 8'b11110000
8'hFF << 3'b101 = 8'b11100000
8'hFF << 3'b110 = 8'b11000000
8'hFF << 3'b111 = 8'b10000000
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
Testing LsV3:
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

import Example5Q::*;

typedef union tagged {
   void    Start;
   Bit#(2) Ignore1; // ignore the initial outputs
   Bit#(3) Ls3;
   Bit#(2) Ignore2;
   Bit#(4) Ls;
   Bit#(4) LsV3;
   void    Done;	      
} State deriving (Eq, Bits);

module mkTb5 (Empty);

   // DUTs

   SShifter#(3,8) ls3();
   mkLs3 the_ls3(ls3);

   SShifter#(4,16) ls();
   mkLs the_ls(ls);

   SMShifter#(4,16) lsv3();
   mkLsV3 the_lsv3(lsv3);

   // Testbench state
   
   Reg#(State) send_state();
   mkReg#(Start) send_state_r(send_state);

   Reg#(State) recv_state();
   mkReg#(Start) recv_state_r(recv_state);

   rule test;
      SXpair#(3,8) ls3_push_val = ?;
      SXpair#(4,16) ls_push_val = ?;
      Maybe#(SXpair#(4,16)) lsv3_push_val = Invalid;
      
      case (send_state) matches

	 tagged Start :
	    begin
	       send_state <= Ls3(0);
	    end

	 tagged Ls3 .s :
	    begin
	       ls3_push_val = tuple2(s, 8'hFF);
	       if (s == 7)
		  send_state <= Ls(0);
	       else
		  send_state <= Ls3(s+1);
	    end

	 tagged Ls .s :
	    begin
	       ls_push_val = tuple2(s, 16'hFFFF);
	       if (s == 15)
		  send_state <= LsV3(0);
	       else
		  send_state <= Ls(s+1);
	    end

	 tagged LsV3 .s :
	    begin
	       lsv3_push_val = Valid(tuple2(s, 16'hFFFF));
	       if (s == 15)
		  send_state <= Done;
	       else
		  send_state <= LsV3(s+1);
	    end

	 default : noAction;

      endcase

      let ls3_ret_val <- ls3.push(ls3_push_val);
      let ls_ret_val <- ls.push(ls_push_val);
      let lsv3_ret_val <- lsv3.push(lsv3_push_val);

      case (recv_state) matches

	 tagged Start :
	    begin
	       $display("Testing Ls3:");
	       recv_state <= Ignore1(3);
	    end

	 tagged Ignore1 .n :
	    begin
	       if (n == 0)
		  recv_state <= Ls3(0);
	       else
		  recv_state <= Ignore1(n-1);
	    end

	 tagged Ls3 .s :
	    begin
	       $display("8'hFF << 3'b%b = 8'b%b", s, ls3_ret_val);
	       if (s == 7) begin
		  recv_state <= Ignore2(0);
		  $display("Testing Ls:");
	       end
	       else
		  recv_state <= Ls3(s+1);
	    end

	 tagged Ignore2 .n :
	    begin
	       if (n == 0)
		  recv_state <= Ls(0);
	       else
		  recv_state <= Ignore2(n-1);
	    end

	 tagged Ls .s :
	    begin
	       $display("16'hFFFF << 4'b%b = 16'b%b", s, ls_ret_val);
	       if (s == 15) begin
		  recv_state <= LsV3(0);
		  $display("Testing LsV3:");
	       end
	       else
		  recv_state <= Ls(s+1);
	    end

	 tagged LsV3 .s :
	    if (isValid(lsv3_ret_val))
	       begin
		  $display("16'hFFFF << 4'b%b = 16'b%b",
		           s, validValue(lsv3_ret_val));
		  if (s == 15) begin
		     $display("Done");
		     $finish(0);
		  end
		  else
		     recv_state <= LsV3(s+1);
	       end

      endcase
      
   endrule

endmodule

