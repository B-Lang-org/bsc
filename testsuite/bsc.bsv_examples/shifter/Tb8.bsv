import Example8::*;

typedef union tagged {
   void    Start;
   Bit#(3) Ignore1; // ignore the initial outputs
   Bit#(4) Ls;
   Bit#(4) LsV3;
   void    Done;	      
} State deriving (Eq, Bits);

module mkTb8 (Empty);

   // DUTs

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
      SXpair#(4,16) ls_push_val = ?;
      Maybe#(SXpair#(4,16)) lsv3_push_val = Invalid;
      
      case (send_state) matches

	 tagged Start :
	    begin
	       send_state <= Ls(0);
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

      let ls_ret_val <- ls.push(ls_push_val);
      let lsv3_ret_val <- lsv3.push(lsv3_push_val);

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

