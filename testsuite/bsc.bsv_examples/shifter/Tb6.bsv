import Example6::*;

typedef union tagged {
   void    Start;
   Bit#(3) General;
} State deriving (Eq, Bits);

module mkTb6 (Empty);

   Reg#(State) state();
   mkReg#(Start) state_r(state);
   
   rule test;
      case (state) matches

	 tagged Start : begin
	    $display("Testing f2:");
	    state <= General(0);
	 end
	 
	 tagged General .s : begin
	    $display("16'hFFFF << 4'b%b = 16'b%b", s, f2(s, 8'hFF));
	    if (s == 7) begin
	       $display("Done");
	       $finish(0);
	    end
	    else
	       state <= General(s+1);
	 end
      endcase
   endrule
   
endmodule

