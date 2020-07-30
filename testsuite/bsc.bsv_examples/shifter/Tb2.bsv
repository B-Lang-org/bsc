import Example2::*;

module mkTb2 (Empty);
   Reg#(Bit#(3)) s();
   mkReg#(0) s_r(s);

   rule test;
      $display("8'b11111111 << 3'b%b = 8'b%b", s, f(s, 8'b11111111));
      if (s == 7)
	 $finish(0);
      s <= s + 1;
   endrule
   
endmodule

