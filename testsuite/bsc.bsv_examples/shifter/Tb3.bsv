import Example3::*;

typedef union tagged {
   void    Start;
   Bit#(3) Static1;
   Bit#(4) General1;
   Bit#(3) Static2;
   Bit#(4) General2;
} State deriving (Eq, Bits);

module mkTb3 (Empty);

   Reg#(State) state();
   mkReg#(Start) state_r(state);
   
   rule test;
      case (state) matches

	 tagged Start : begin
	    $display("Testing f_3bit:");
	    state <= Static1(0);
	 end
	 
	 tagged Static1 .s : begin
	    $display("8'hFF << 3'b%b = 8'b%b", s, f_3bit(s, 8'hFF));
	    if (s == 7) begin
	       $display("Testing f:");
	       state <= General1(0);
	    end
	    else
	       state <= Static1(s+1);
	 end

	 tagged General1 .s : begin
	    $display("16'hFFFF << 4'b%b = 16'b%b", s, f(s, 16'hFFFF));
	    if (s == 15) begin
	       $display("Testing f2_3bit:");
	       state <= Static2(0);
	    end
	    else
	       state <= General1(s+1);
	 end

	 tagged Static2 .s : begin
	    $display("8'hFF << 3'b%b = 8'b%b", s, f2_3bit(s, 8'hFF));
	    if (s == 7) begin
	       $display("Testing f2:");
	       state <= General2(0);
	    end
	    else
	       state <= Static2(s+1);
	 end

	 tagged General2 .s : begin
	    $display("16'hFFFF << 4'b%b = 16'b%b", s, f2(s, 16'hFFFF));
	    if (s == 15) begin
	       $display("Done");
	       $finish(0);
	    end
	    else
	       state <= General2(s+1);
	 end

      endcase
   endrule
   
endmodule

